/-
  Nitro protocol theorems: unbeatable strategies, finalizability, value
  algorithms, ledger and virtual channel constructions, and the SATP
  protocol guarantees. Every proof is `sorry`, except the theorems that read
  no game definition. Each doc comment cites the source lines and the
  property ids of `docs/nitro-theorems.md`. The repair of 2026-10-27 (every
  changed type, with its reason) is `docs/nitro-repair-2026-10-27.md`.
-/
import ArmadaLean.Nitro.Safety
import ArmadaLean.Nitro.Reachable

namespace ArmadaLean.Nitro

variable {E : Type} [DecidableEq E]

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
    simpa [FixedPart.address_eq] using hf
  have hfin : (s.statusOf c).mode s.now = .finalized := by
    rw [ChannelStatus.mode_eq_finalized_iff, hf0]; rfl
  cases op with
  | deposit a e x =>
    obtain ⟨⟨c', hac', -⟩, -, hb, -, hs, hn⟩ := Adjudicator.deposit_some h
    have had : a ≠ (Address.external d : Address E) := by rw [hac']; intro hh; cases hh
    refine ⟨o, amt, ?_, ?_, hd, ?_⟩
    · simpa [FixedPart.address_eq, Adjudicator.statusOf_of_status hs, hn] using hf
    · rw [hb, Balances.get_add]
      by_cases hca : c.address = a
      · rw [if_pos hca]; grind
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
        simp [FixedPart.address_eq, hstatc]
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
          have heq : o.owed (Address.external d) = amt := by simp [Allocation.owed, hd]
          rw [heq] at hxb; exact hxb
        refine ⟨o.reduceOwed (Address.external d) x, amt - x, hfo', ?_, hfind', ?_⟩
        · rw [hbal, Balances.get_sub, if_pos rfl]
          by_cases hba : (Address.external d : Address E) = a.address
          · rw [hba, Balances.get_add, if_pos rfl]; grind
          · rw [Balances.get_add, if_neg (Ne.symm hba)]; grind
        · rw [hbal, Balances.get_sub, if_neg hcd, Balances.get_add, if_pos rfl]
          grind
      · rw [if_neg hbd] at hfind'
        refine ⟨o.reduceOwed b x, amt, hfo', ?_, by rw [hfind']; exact hd, ?_⟩
        · rw [hbal, Balances.get_sub, if_pos rfl]
          by_cases hba : b = a.address
          · rw [hba, Balances.get_add, if_pos rfl]; grind
          · rw [Balances.get_add, if_neg (Ne.symm hba)]; grind
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
      · simpa [FixedPart.address_eq, hstatc, hnow] using hf
      · rw [hbal, Balances.get_sub, if_neg haddr, Balances.get_add]
        by_cases hbc : c.address = b
        · rw [if_pos hbc]; grind
        · rw [if_neg hbc]; exact ht
      · rw [hbal, Balances.get_sub, if_neg hcd, Balances.get_add]
        by_cases hbd : (Address.external d : Address E) = b
        · rw [if_pos hbd]; grind
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
        simp [FixedPart.address_eq, hstatl]
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
        · rw [if_pos hld, ← hld, Allocation.find_addTo_self, hd]; simp
        · rw [if_neg hld, Allocation.find_addTo_of_ne _ _ hld, hd]
      have hfind2 : ((o.addTo left (oV.amountAt 0)).addTo right (oV.amountAt 1)).find
          (Address.external d) = some ⟨Address.external d, .alloc
            ((if (Address.external d : Address E) = left then amt + oV.amountAt 0 else amt) +
              (if (Address.external d : Address E) = right then oV.amountAt 1 else 0))⟩ := by
        by_cases hrd : (Address.external d : Address E) = right
        · rw [if_pos hrd, ← hrd, Allocation.find_addTo_self, hfind1]; simp
        · rw [if_neg hrd, Allocation.find_addTo_of_ne _ _ hrd, hfind1]; simp
      have hfind3 : (((o.addTo left (oV.amountAt 0)).addTo right (oV.amountAt 1)).remove
          v.address).find (Address.external d) = some ⟨Address.external d, .alloc
            ((if (Address.external d : Address E) = left then amt + oV.amountAt 0 else amt) +
              (if (Address.external d : Address E) = right then oV.amountAt 1 else 0))⟩ := by
        rw [Allocation.find_remove, if_neg had, hfind2]
      refine ⟨_, _, hfo', ?_, hfind3, ?_⟩
      · rw [hbal']; grind
      · rw [hbal']
        split <;> split <;> grind
    · obtain ⟨oL, oV, x, left, right, hL, hV, hfind, -, -, hxeq, hsucc, hlk, hvk⟩ :=
        Adjudicator.reclaim_some h
      have hstatc : s'.statusOf c = s.statusOf c := by
        rw [hsucc, Adjudicator.statusOf_setStatus, if_neg (Ne.symm hcl)]
      have hnow : s'.now = s.now := by rw [hsucc]; rfl
      have hbal' : s'.balances = s.balances := by rw [hsucc]; rfl
      refine ⟨o, amt, ?_, ?_, hd, ?_⟩
      · simpa [FixedPart.address_eq, hstatc, hnow] using hf
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
      · simpa [FixedPart.address_eq, hstatc, hnow] using hf
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
      · simpa [FixedPart.address_eq, hstatc, hnow] using hf
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
      · simpa [FixedPart.address_eq, hstatc, hnow] using hf
      · rw [hbal']; exact ht
      · rw [hbal']
  | tick dt =>
    have hs' : s.tick dt = s' := by simpa using h
    subst hs'
    refine ⟨o, amt, ?_, ?_, hd, ?_⟩
    · simpa [FixedPart.address_eq] using
        ChannelStatus.finalOutcome_mono hf0 (Nat.le_add_right s.now dt)
    · simpa using ht
    · simp

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

/-- An adversary move never moves the chain's clock backward: only `tick`
    touches it, and only forward (`Adjudicator.apply_now_le`). -/
theorem NetworkState.applyAdv_now_le (apps : Apps E) {p : Participant}
    (net : NetworkState E p) (m : AdvMove E) :
    net.chain.now ≤ (net.applyAdv apps m).chain.now := by
  cases m with
  | chain caller op =>
    simp only [NetworkState.applyAdv]
    cases h : net.chain.apply apps caller op with
    | none => exact le_refl _
    | some s' => simpa using Adjudicator.apply_now_le h
  | deliver ss => exact le_refl _
  | tick dt => simp only [NetworkState.applyAdv, Adjudicator.tick_now]; exact Nat.le_add_right _ _
  | land op =>
    simp only [NetworkState.applyAdv]
    cases h : net.chain.apply apps p op with
    | none => exact le_refl _
    | some s' => simpa using Adjudicator.apply_now_le h

/-- Over a round's adversary play (`Threat.RoundSeq`, any pending calls),
    the chain's clock only advances (`NetworkState.applyAdv_now_le`, by
    induction over `land`/`tick`/`other`: each is one `NetworkState.applyAdv`
    step). -/
theorem Threat.RoundSeq.now_le {apps : Apps E} {p : Participant} {T : Threat E p} {t : Time}
    {pending : List (Op E)} {net net' : NetworkState E p}
    (h : T.RoundSeq apps t pending net net') : net.chain.now ≤ net'.chain.now := by
  induction h with
  | nil => exact le_refl _
  | land _ _ ih => exact le_trans (NetworkState.applyAdv_now_le _ _ _) ih
  | tick _ _ _ ih => exact le_trans (NetworkState.applyAdv_now_le _ _ _) ih
  | other _ _ _ _ ih => exact le_trans (NetworkState.applyAdv_now_le _ _ _) ih

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
    | deliver ss => simp [NetworkState.applyAdv]
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
          simp [NetworkState.applyAdv, happly]
        have hmono := hrest.balances_external_mono d
        rw [hchain] at hmono
        have hcne : (Address.external d : Address E) ≠ c.address := by
          rw [FixedPart.address_eq]; intro hh; cases hh
        rw [hbal, if_neg hcne] at hmono
        have hpaid : amt ≤ o.paidTo (net1.chain.balances.get c.address) (Address.external d) := by
          have hsub : o.dedup.total ≤ o.total :=
            Allocation.total_le_of_sublist (Allocation.dedupFrom_sublist [] o)
          have hdedup_le : o.dedup.total ≤ net1.chain.balances.get c.address := le_trans hsub ht
          have howed1 : o.owed (Address.external d) = amt := by simp [Allocation.owed, hd]
          have hdedup_owed : o.dedup.owed (Address.external d) = amt := by
            rw [Allocation.owed_dedup]; exact howed1
          have hle := Allocation.owed_le_payout_get hdedup_le (Address.external d)
          rw [hdedup_owed] at hle
          rwa [Allocation.paidTo_eq_get]
        grind
      · simp at hsplit
    · simp at hsplit
  | @tick pending net1 net2 dt hfeas hgate hrest ih =>
    intro o amt hf ht hd
    refine ih hp ?_ ?_ hd
    · simpa [NetworkState.applyAdv, FixedPart.address_eq] using
        ChannelStatus.finalOutcome_mono
          (show (net1.chain.statusOf c).finalOutcome net1.chain.now = some (.allocation o) by
            simpa [FixedPart.address_eq] using hf)
          (Nat.le_add_right net1.chain.now dt)
    · simpa [NetworkState.applyAdv] using ht
  | @other pending net1 net2 m hfeas hnotick hnoland hrest ih =>
    intro o amt hf ht hd
    cases m with
    | chain caller op =>
      cases hm : net1.chain.apply apps caller op with
      | none =>
        have := ih hp (by simp only [NetworkState.applyAdv, hm]; exact hf)
          (by simp only [NetworkState.applyAdv, hm]; exact ht) hd
        simpa [NetworkState.applyAdv, hm] using this
      | some s' =>
        obtain ⟨o1, amt1, hf1, ht1, hd1, hle1⟩ := directly_funded_step hf ht hd hm
        have := ih hp (by simp only [NetworkState.applyAdv, hm]; exact hf1)
          (by simp only [NetworkState.applyAdv, hm]; exact ht1) hd1
        have heq : (NetworkState.applyAdv apps (AdvMove.chain caller op) net1).chain.balances.get
            (Address.external d) = s'.balances.get (Address.external d) := by
          simp [NetworkState.applyAdv, hm]
        rw [heq] at this
        exact le_trans hle1 this
    | deliver ss =>
      have := ih hp (by simp only [NetworkState.applyAdv]; exact hf)
        (by simp only [NetworkState.applyAdv]; exact ht) hd
      simpa [NetworkState.applyAdv] using this
    | tick dt => exact absurd rfl (hnotick dt)
    | land op => exact absurd rfl (hnoland op)

/-- Nitro-16, Nitro-21, ForceMove-B01, ForceMove-C03, docs-0070-05, docs-0080-06. Nitro:395-398: "where
    the channel L itself has enough coins in the adjudicator to cover the
    entire allocation ... A will receive all x coins allocated to them in ω."
    The strategy is one transfer. The entry of `d` is an allocation item:
    go-nitro refuses to transfer a guarantee (MultiAssetHolder.sol:169-170).

    Operator ruling 2026-10-29: `net` is a reachable network state
    (`Nitro.participant_chain_reachable`); a reachable chain never pays a
    virtual-kind channel's own balance out through `d` (the unreachable
    counterexample put coins in a virtual-kind channel,
    `Reachable.balances_virtual_zero`). -/
theorem directly_funded_pays (apps : Apps E) {p : Participant} (T : Threat E p)
    (A : Assumptions apps p T) (net : NetworkState E p)
    (hr : (Nitro.participant apps T).Reachable net) (c : FixedPart) (o : Allocation E) (d : E)
    (hf : net.chain.finalOutcome c.address = some (.allocation o))
    (hfund : net.chain.DirectlyFunded c) (amt : Coins)
    (hd : o.find (.external d) = some ⟨.external d, .alloc amt⟩) :
    UnbeatableNoWait apps T
      (fun net' => net.chain.balances.get (.external d) + o.owed (.external d) ≤
        net'.chain.balances.get (.external d)) net := by
  have hrc : Reachable apps net.chain := Nitro.participant_chain_reachable hr
  obtain ⟨o', hfo', htot'⟩ := hfund
  rw [hf] at hfo'
  simp only [Option.some.injEq, Outcome.allocation.injEq] at hfo'
  subst hfo'
  have howed : o.owed (Address.external d) = amt := by simp [Allocation.owed, hd]
  rw [howed]
  cases hk : c.kind with
  | virtual =>
    have hzero : net.chain.balances.get (Address.channel c) = 0 :=
      Reachable.balances_virtual_zero hrc c hk
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
      (by simp [Op.HonestFeasible, Op.proofStates]) ?_
    intro net' hround
    obtain ⟨hseq, -⟩ := hround
    simp only [HonestMove.calls_chain] at hseq
    have hle := directly_funded_round c d hk net net' _ rfl hseq hf htot' hd
    apply UnbeatableIn.done
    simpa using hle

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
    (hseq : Threat.RoundSeq apps T t [Op.conclude c ss] net net') :
    net'.chain.now < net.chain.now + T.ε →
    (∀ t0 ∈ net.sent, t0.state.channel = c → t0.state.isFinal = true → t0.state.outcome = Ω) →
    (net.chain.finalizedWith c.address = some Ω ∨ (net.chain.statusOf c).IsOpen net'.chain.now) →
    net'.chain.finalizedWith c.address = some Ω := by
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
              simpa [FixedPart.address_eq, Adjudicator.finalizedWith_channel] using hfz
            have hmode1 : (net1.chain.statusOf c).mode net1.chain.now = .finalized := by
              rw [ChannelStatus.mode_eq_finalized_iff, ← ChannelStatus.finalizedWith_isSome_iff,
                hfz1]
              rfl
            have hnopen : ¬ (net1.chain.statusOf c).IsOpen net1.chain.now := by
              rw [ChannelStatus.isOpen_iff_ne, not_not]; exact hmode1
            cases hop : net1.chain.apply apps p (Op.conclude c ss) with
            | none => simpa [NetworkState.applyAdv, hop] using hfz
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
            simpa [FixedPart.address_eq, Adjudicator.finalizedWith_channel,
              Adjudicator.statusOf_setStatus, ChannelStatus.finalizedWith_finalized] using hΩeq
        exact hrest.finalizedWith_mono hland
      · simp at hsplit
    · simp at hsplit
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
      · exact Or.inr (by simpa [NetworkState.applyAdv, Adjudicator.tick_statusOf] using h)
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
        | none => simpa using hbase1
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
              have hs' : net1.chain.tick dt' = s' := by simpa using h
              subst hs'
              exact Or.inr (by rw [Adjudicator.tick_statusOf]; exact hop)
            | transfer a b =>
              by_cases hac : a = c
              · subst hac
                obtain ⟨o, -, -, hfo, -, -, -, -, -, -, -, -⟩ := Adjudicator.transfer_some h
                rw [hfo1] at hfo; exact absurd hfo (by simp)
              · obtain ⟨_, _, _, _, _, _, _, _, hs, _, _, _⟩ := Adjudicator.transfer_some h
                exact Or.inr (by
                  rw [Adjudicator.statusOf_of_status hs, Adjudicator.statusOf_setStatus,
                    if_neg (Ne.symm hac)]
                  exact hop)
            | reclaim l v =>
              by_cases hlc : l = c
              · subst hlc
                obtain ⟨oL, -, -, -, -, hfo, -, -, -, -, -, -, -, -⟩ := Adjudicator.reclaim_some h
                rw [hfo1] at hfo; exact absurd hfo (by simp)
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
                simp [ChannelStatus.IsOpen, ChannelStatus.mode, not_le.mpr hdlt]
              · obtain ⟨-, rfl⟩ := Adjudicator.challenge_some h
                exact Or.inr (by
                  rw [Adjudicator.statusOf_setStatus, if_neg (Ne.symm hcc)]; exact hop)
            | checkpoint c' proof candidate =>
              by_cases hcc : c' = c
              · subst hcc
                obtain ⟨-, rfl⟩ := Adjudicator.checkpoint_some h
                refine Or.inr ?_
                rw [Adjudicator.statusOf_setStatus, if_pos rfl]
                simp [ChannelStatus.IsOpen, ChannelStatus.mode]
              · obtain ⟨-, rfl⟩ := Adjudicator.checkpoint_some h
                exact Or.inr (by
                  rw [Adjudicator.statusOf_setStatus, if_neg (Ne.symm hcc)]; exact hop)
            | conclude c' ss' =>
              by_cases hcc : c' = c
              · subst hcc
                obtain ⟨⟨-, hproof'⟩, rfl⟩ := Adjudicator.conclude_some h
                refine Or.inl ?_
                have hp' : p ∈ ss'.signers := hproof'.2.2 p (hproof'.1 ▸ hp)
                have hmem : ss' ∈ (Op.conclude c' ss').proofStates := by simp [Op.proofStates]
                have := (hbounds.unforgeable net1 caller (.conclude c' ss') hfeas ss' hmem).1 hp'
                obtain ⟨t', htmem, hteq⟩ := this
                have hΩ' := hsent t' htmem (hteq ▸ hproof'.1) (hteq ▸ hproof'.2.1)
                simp [Adjudicator.finalizedWith_channel, hteq ▸ hΩ']
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
    (hseq : Threat.RoundSeq apps T net.chain.now [Op.conclude c ss] net net')
    (hεbound : net'.chain.now < net.chain.now + T.ε)
    (hsent : ∀ t ∈ net.sent, t.state.channel = c → t.state.isFinal = true → t.state.outcome = Ω)
    (hopen : net.chain.finalizedWith c.address = none) (hpend : net.DeadlineAfter c T.ε) :
    net'.chain.finalizedWith c.address = some Ω := by
  have hbase : net.chain.finalizedWith c.address = some Ω ∨
      (net.chain.statusOf c).IsOpen net'.chain.now := by
    right
    rcases hstat : net.chain.statusOf c with t | ⟨t, ch⟩ | ⟨t, f, o⟩
    · simp [ChannelStatus.IsOpen, ChannelStatus.mode]
    · have hdl := hpend t ch hstat
      have hnf : ¬ (ch.deadline ≤ net'.chain.now) := by
        intro hle
        exact absurd (le_trans hdl hle) (not_le.mpr hεbound)
      simp [ChannelStatus.IsOpen, ChannelStatus.mode, hnf]
    · exfalso
      have hfw : net.chain.finalizedWith c.address = some f := by
        simp only [FixedPart.address_eq, Adjudicator.finalizedWith_channel, hstat,
          ChannelStatus.finalizedWith_finalized]
      rw [hopen] at hfw
      exact absurd hfw (by simp)
  exact round_keeps_status hbounds hp hdur hproof hΩ net net' net.chain.now rfl hseq hεbound
    hsent hbase

/-- Nitro-13, Nitro-21, Nitro-23, docs-0070-05, ForceMove-A14. SATP:286-289: a
    final state supported by all finalizes "without delay"; Nitro:296-299: a
    participant who holds a conclusion proof can register it; go-nitro
    `_conclude` accepts it from any caller. Under the consensus app no other
    participant can finalize a different outcome without `p`'s signature
    before `p`'s conclude lands, because a challenge lasts at least `2 * ε`
    and no running challenge ends within `ε` (Nitro:537-539). -/
theorem conclusion_proof_finalizable (apps : Apps E) {p : Participant} (T : Threat E p)
    (A : Assumptions apps p T) (net : NetworkState E p)
    (_hr : (Nitro.participant apps T).Reachable net) (c : FixedPart) (ss : SignedState E)
    (Ω : Outcome E) (hc : apps c.appDef = consensusRules) (hp : p ∈ c.participants)
    (hh : net.Holds ss) (hproof : ConclusionProof c ss) (hΩ : ss.state.outcome = Ω)
    (hsent : ∀ t ∈ net.sent, t.state.channel = c → t.state.isFinal = true → t.state.outcome = Ω)
    (hchain : net.chain.finalizedWith c.address = none ∨ net.Finalized c Ω)
    (hdur : 2 * T.ε ≤ c.challengeDuration) (hpend : net.DeadlineAfter c T.ε) :
    UnbeatableNoWait apps T (fun net' => net'.Finalized c Ω) net := by
  rcases hchain with h1 | h2
  · refine UnbeatableIn.move (.chain (.conclude c ss)) trivial
      (by simpa [HonestMove.Feasible_chain, Op.HonestFeasible, Op.proofStates] using hh) ?_
    intro net' hround
    obtain ⟨hseq, hεbound⟩ := hround
    simp only [HonestMove.calls_chain] at hseq
    have hfinal := conclude_round_finalized A.toBounds hp hdur hproof hΩ hseq hεbound hsent h1
      hpend
    apply UnbeatableIn.done
    show (net'.applyHonest (.chain (.conclude c ss))).Finalized c Ω
    simpa [NetworkState.Finalized, FixedPart.address_eq, Adjudicator.finalizedWith_channel]
      using hfinal
  · exact UnbeatableIn.done h2

/-- Over a round's play with nothing of `p`'s own still pending, "finalized
    with `ss.state.outcome`, or challenged at a turn at or above
    `ss.state.turnNum`, matching `ss.state`, with a deadline still ahead" is
    preserved: the turn-bound argument (`hbounds.unforgeable`, `hlatest`)
    bounds any OTHER candidate's turn at or below `ss.state.turnNum`, so no
    fresh `challenge` or `checkpoint` can push the record past where it
    already sits. A `conclude` needs `p`'s own signature on a final state,
    which `hfinal` ties to `ss.state.outcome`. Restated against the
    explicit-time game (operator ruling 2026-10-29): the invariant drops
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
  intro net net' t hseq
  generalize hpnil : ([] : List (Op E)) = pending at hseq
  induction hseq with
  | nil => intro _ _ _ hbase; exact hbase
  | land hsplit _ _ => rw [← hpnil] at hsplit; simp at hsplit
  | @tick pending net1 net2 dt hfeas hgate hrest ih =>
    intro hεbound hlatest hfinal hbase
    have step : (net1.chain.finalizedWith c.address = some ss.state.outcome ∨
        ∃ T0 ch, net1.chain.statusOf c = .challenged T0 ch ∧ ss.state.turnNum ≤ T0 ∧
          ch.state = ss.state ∧ net2.chain.now < ch.deadline) →
        ((net1.applyAdv apps (AdvMove.tick dt)).chain.finalizedWith c.address =
          some ss.state.outcome ∨
        ∃ T0 ch, (net1.applyAdv apps (AdvMove.tick dt)).chain.statusOf c = .challenged T0 ch ∧
          ss.state.turnNum ≤ T0 ∧ ch.state = ss.state ∧ net2.chain.now < ch.deadline) := by
      intro hbase1
      rcases hbase1 with hf | ⟨T0, ch, hst, hT0, hchs, hdd⟩
      · exact Or.inl (by
          simpa [NetworkState.applyAdv, FixedPart.address_eq] using
            ChannelStatus.finalizedWith_mono (by simpa [FixedPart.address_eq] using hf)
              (Nat.le_add_right _ dt))
      · exact Or.inr ⟨T0, ch, by simpa [NetworkState.applyAdv] using hst, hT0, hchs, hdd⟩
    have hbase' := step hbase
    have hεbound' : net2.chain.now < (net1.applyAdv apps (AdvMove.tick dt)).chain.now + T.ε :=
      lt_of_lt_of_le hεbound
        (Nat.add_le_add_right (NetworkState.applyAdv_now_le apps net1 (.tick dt)) T.ε)
    have hlatest' : ∀ t0 ∈ (net1.applyAdv apps (AdvMove.tick dt)).sent, t0.state.channel = c →
        t0.state.turnNum < ss.state.turnNum ∨ t0.state = ss.state := by
      rw [NetworkState.applyAdv_sent]; exact hlatest
    have hfinal' : ∀ t0 ∈ (net1.applyAdv apps (AdvMove.tick dt)).sent, t0.state.channel = c →
        t0.state.isFinal = true → t0.state.outcome = ss.state.outcome := by
      rw [NetworkState.applyAdv_sent]; exact hfinal
    exact ih hpnil hεbound' hlatest' hfinal' hbase'
  | @other pending net1 net2 m hfeas hnotick hnoland hrest ih =>
    intro hεbound hlatest hfinal hbase
    have hsupp : ∀ (proof : SupportProof E) (cand : State E),
        (∀ ss' ∈ proof, p ∈ ss'.signers → ∃ x ∈ net1.sent, x.state = ss'.state) →
        (apps c.appDef).supports c proof cand = true →
        cand.turnNum < ss.state.turnNum ∨ cand = ss.state := by
      intro proof cand hU hs
      rw [hc] at hs
      match proof, hs with
      | [ss'], hs =>
        simp only [consensusRules, Bool.and_eq_true, decide_eq_true_eq] at hs
        obtain ⟨⟨hss', hch⟩, hall'⟩ := hs
        obtain ⟨x, hx, hxs⟩ := hU ss' (List.mem_singleton_self _) (hall' p (hch ▸ hp))
        have hb := hlatest x hx (by rw [hxs]; exact hch)
        rw [hxs, hss'] at hb
        exact hb
    have step : (net1.chain.finalizedWith c.address = some ss.state.outcome ∨
        ∃ T0 ch, net1.chain.statusOf c = .challenged T0 ch ∧ ss.state.turnNum ≤ T0 ∧
          ch.state = ss.state ∧ net2.chain.now < ch.deadline) →
        ((net1.applyAdv apps m).chain.finalizedWith c.address = some ss.state.outcome ∨
        ∃ T0 ch, (net1.applyAdv apps m).chain.statusOf c = .challenged T0 ch ∧
          ss.state.turnNum ≤ T0 ∧ ch.state = ss.state ∧ net2.chain.now < ch.deadline) := by
      intro hbase1
      cases m with
      | tick dt => exact absurd rfl (hnotick dt)
      | land op => exact absurd rfl (hnoland op)
      | deliver ss' => exact hbase1
      | chain caller op =>
        rcases hbase1 with hf | ⟨T0, ch, hst, hT0, hchs, hdd⟩
        · refine Or.inl ?_
          simp only [NetworkState.applyAdv]
          cases h : net1.chain.apply apps caller op with
          | none => simpa using hf
          | some s' => exact Adjudicator.finalizedWith_apply h hf
        · have hmono : net1.chain.now ≤ net2.chain.now :=
            le_trans (NetworkState.applyAdv_now_le apps net1 (.chain caller op)) hrest.now_le
          have hltdl : net1.chain.now < ch.deadline := lt_of_le_of_lt hmono hdd
          have hm1 : net1.chain.mode c = .challenge := by
            rw [Adjudicator.mode_eq, hst, ChannelStatus.mode_challenged, if_neg (not_le.mpr hltdl)]
          simp only [NetworkState.applyAdv]
          cases h : net1.chain.apply apps caller op with
          | none => exact Or.inr ⟨T0, ch, hst, hT0, hchs, hdd⟩
          | some s' =>
            have hfo1 : net1.chain.finalOutcome c.address = none := by
              simp only [FixedPart.address_eq, Adjudicator.finalOutcome_channel, hst,
                ChannelStatus.finalOutcome_challenged, if_neg (not_le.mpr hltdl)]
            have hU : ∀ ss' ∈ op.proofStates, p ∈ ss'.signers →
                ∃ x ∈ net1.sent, x.state = ss'.state :=
              fun ss' hmem hsig => (hbounds.unforgeable net1 caller op hfeas ss' hmem).1 hsig
            cases op with
            | deposit a e x =>
              obtain ⟨-, -, -, -, hs, -⟩ := Adjudicator.deposit_some h
              exact Or.inr ⟨T0, ch, by rw [Adjudicator.statusOf_of_status hs]; exact hst, hT0,
                hchs, hdd⟩
            | tick dt =>
              have hs' : net1.chain.tick dt = s' := by simpa using h
              subst hs'
              exact Or.inr ⟨T0, ch, by rw [Adjudicator.tick_statusOf]; exact hst, hT0, hchs, hdd⟩
            | transfer a b =>
              by_cases hac : a = c
              · subst hac
                obtain ⟨o, -, -, hfo, -, -, -, -, -, -, -, -⟩ := Adjudicator.transfer_some h
                rw [hfo1] at hfo; exact absurd hfo (by simp)
              · obtain ⟨_, _, _, _, _, _, _, _, hs, _, _, _⟩ := Adjudicator.transfer_some h
                exact Or.inr ⟨T0, ch, by
                  rw [Adjudicator.statusOf_of_status hs, Adjudicator.statusOf_setStatus,
                    if_neg (Ne.symm hac)]; exact hst, hT0, hchs, hdd⟩
            | reclaim l v =>
              by_cases hlc : l = c
              · subst hlc
                obtain ⟨oL, -, -, -, -, hfo, -, -, -, -, -, -, -, -⟩ := Adjudicator.reclaim_some h
                rw [hfo1] at hfo; exact absurd hfo (by simp)
              · obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hsr, _, _⟩ := Adjudicator.reclaim_some h
                exact Or.inr ⟨T0, ch, by
                  rw [hsr, Adjudicator.statusOf_setStatus, if_neg (Ne.symm hlc)]; exact hst, hT0,
                  hchs, hdd⟩
            | challenge c' proof cand =>
              by_cases hcc : c' = c
              · exfalso; subst hcc
                obtain ⟨⟨-, hs, -, hmode⟩, -⟩ := Adjudicator.challenge_some h
                rcases hmode with ⟨hmo, -⟩ | ⟨-, hlt2⟩
                · rw [hm1] at hmo; exact absurd hmo (by decide)
                · rw [hst, ChannelStatus.turnNumRecord_challenged] at hlt2
                  rcases hsupp proof cand hU hs with hlt3 | heqc3
                  · omega
                  · rw [heqc3] at hlt2; omega
              · obtain ⟨-, rfl⟩ := Adjudicator.challenge_some h
                exact Or.inr ⟨T0, ch, by
                  rw [Adjudicator.statusOf_setStatus, if_neg (Ne.symm hcc)]; exact hst, hT0, hchs,
                  hdd⟩
            | checkpoint c' proof cand =>
              by_cases hcc : c' = c
              · exfalso; subst hcc
                obtain ⟨⟨-, hs, -, hlt2⟩, -⟩ := Adjudicator.checkpoint_some h
                rw [hst, ChannelStatus.turnNumRecord_challenged] at hlt2
                rcases hsupp proof cand hU hs with hlt3 | heqc3
                · omega
                · rw [heqc3] at hlt2; omega
              · obtain ⟨-, rfl⟩ := Adjudicator.checkpoint_some h
                exact Or.inr ⟨T0, ch, by
                  rw [Adjudicator.statusOf_setStatus, if_neg (Ne.symm hcc)]; exact hst, hT0, hchs,
                  hdd⟩
            | conclude c' ss' =>
              by_cases hcc : c' = c
              · subst hcc
                obtain ⟨⟨-, hproof'⟩, rfl⟩ := Adjudicator.conclude_some h
                refine Or.inl ?_
                have hp' : p ∈ ss'.signers := hproof'.2.2 p (hproof'.1 ▸ hp)
                have hmem : ss' ∈ (Op.conclude c' ss').proofStates := by simp [Op.proofStates]
                obtain ⟨x, hxmem, hxeq⟩ := hU ss' hmem hp'
                have hΩ' := hfinal x hxmem (hxeq ▸ hproof'.1) (hxeq ▸ hproof'.2.1)
                simp [Adjudicator.finalizedWith_channel, hxeq ▸ hΩ']
              · obtain ⟨-, rfl⟩ := Adjudicator.conclude_some h
                exact Or.inr ⟨T0, ch, by
                  rw [Adjudicator.statusOf_setStatus, if_neg (Ne.symm hcc)]; exact hst, hT0, hchs,
                  hdd⟩
    have hbase' := step hbase
    have hεbound' : net2.chain.now < (net1.applyAdv apps m).chain.now + T.ε :=
      lt_of_lt_of_le hεbound (Nat.add_le_add_right (NetworkState.applyAdv_now_le apps net1 m) T.ε)
    have hlatest' : ∀ t0 ∈ (net1.applyAdv apps m).sent, t0.state.channel = c →
        t0.state.turnNum < ss.state.turnNum ∨ t0.state = ss.state := by
      rw [NetworkState.applyAdv_sent]; exact hlatest
    have hfinal' : ∀ t0 ∈ (net1.applyAdv apps m).sent, t0.state.channel = c →
        t0.state.isFinal = true → t0.state.outcome = ss.state.outcome := by
      rw [NetworkState.applyAdv_sent]; exact hfinal
    exact ih hpnil hεbound' hlatest' hfinal' hbase'

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
    (hc : apps c.appDef = consensusRules) (hp : p ∈ c.participants)
    (hdur : 2 * T.ε ≤ c.challengeDuration) :
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
  intro net net' t hseq hDbound
  generalize hpnil : ([] : List (Op E)) = pending at hseq
  induction hseq with
  | nil => intro _ _ _ hbase; exact hbase
  | land hsplit _ _ => rw [← hpnil] at hsplit; simp at hsplit
  | @tick pending net1 net2 dt hfeas hgate hrest ih =>
    intro hεbound hlatest hfinal hbase
    have step : (net1.chain.finalizedWith c.address = some ss.state.outcome ∨
        (∃ t0, net1.chain.statusOf c = .open t0 ∧ t0 ≤ ss.state.turnNum) ∨
        (∃ t0 ch, net1.chain.statusOf c = .challenged t0 ch ∧
          (t0 < ss.state.turnNum ∨ ch.state = ss.state) ∧ D < ch.deadline)) →
        ((net1.applyAdv apps (AdvMove.tick dt)).chain.finalizedWith c.address =
          some ss.state.outcome ∨
        (∃ t0, (net1.applyAdv apps (AdvMove.tick dt)).chain.statusOf c = .open t0 ∧
          t0 ≤ ss.state.turnNum) ∨
        (∃ t0 ch, (net1.applyAdv apps (AdvMove.tick dt)).chain.statusOf c = .challenged t0 ch ∧
          (t0 < ss.state.turnNum ∨ ch.state = ss.state) ∧ D < ch.deadline)) := by
      intro hbase1
      rcases hbase1 with hf | ⟨t0, ho, hle⟩ | ⟨t0, ch, hst, hdis, hdd⟩
      · exact Or.inl (by
          simpa [NetworkState.applyAdv, FixedPart.address_eq] using
            ChannelStatus.finalizedWith_mono (by simpa [FixedPart.address_eq] using hf)
              (Nat.le_add_right _ dt))
      · exact Or.inr (Or.inl ⟨t0, by simpa [NetworkState.applyAdv] using ho, hle⟩)
      · exact Or.inr (Or.inr ⟨t0, ch, by simpa [NetworkState.applyAdv] using hst, hdis, hdd⟩)
    have hbase' := step hbase
    have hεbound' : D < (net1.applyAdv apps (AdvMove.tick dt)).chain.now + T.ε :=
      lt_of_lt_of_le hεbound
        (Nat.add_le_add_right (NetworkState.applyAdv_now_le apps net1 (.tick dt)) T.ε)
    have hlatest' : ∀ t0 ∈ (net1.applyAdv apps (AdvMove.tick dt)).sent, t0.state.channel = c →
        t0.state.turnNum < ss.state.turnNum ∨ t0.state = ss.state := by
      rw [NetworkState.applyAdv_sent]; exact hlatest
    have hfinal' : ∀ t0 ∈ (net1.applyAdv apps (AdvMove.tick dt)).sent, t0.state.channel = c →
        t0.state.isFinal = true → t0.state.outcome = ss.state.outcome := by
      rw [NetworkState.applyAdv_sent]; exact hfinal
    exact ih hDbound hpnil hεbound' hlatest' hfinal' hbase'
  | @other pending net1 net2 m hfeas hnotick hnoland hrest ih =>
    intro hεbound hlatest hfinal hbase
    have hsupp : ∀ (proof : SupportProof E) (cand : State E),
        (∀ ss' ∈ proof, p ∈ ss'.signers → ∃ x ∈ net1.sent, x.state = ss'.state) →
        (apps c.appDef).supports c proof cand = true →
        cand.turnNum < ss.state.turnNum ∨ cand = ss.state := by
      intro proof cand hU hs
      rw [hc] at hs
      match proof, hs with
      | [ss'], hs =>
        simp only [consensusRules, Bool.and_eq_true, decide_eq_true_eq] at hs
        obtain ⟨⟨hss', hch⟩, hall'⟩ := hs
        obtain ⟨x, hx, hxs⟩ := hU ss' (List.mem_singleton_self _) (hall' p (hch ▸ hp))
        have hb := hlatest x hx (by rw [hxs]; exact hch)
        rw [hxs, hss'] at hb
        exact hb
    have step : (net1.chain.finalizedWith c.address = some ss.state.outcome ∨
        (∃ t0, net1.chain.statusOf c = .open t0 ∧ t0 ≤ ss.state.turnNum) ∨
        (∃ t0 ch, net1.chain.statusOf c = .challenged t0 ch ∧
          (t0 < ss.state.turnNum ∨ ch.state = ss.state) ∧ D < ch.deadline)) →
        ((net1.applyAdv apps m).chain.finalizedWith c.address = some ss.state.outcome ∨
        (∃ t0, (net1.applyAdv apps m).chain.statusOf c = .open t0 ∧ t0 ≤ ss.state.turnNum) ∨
        (∃ t0 ch, (net1.applyAdv apps m).chain.statusOf c = .challenged t0 ch ∧
          (t0 < ss.state.turnNum ∨ ch.state = ss.state) ∧ D < ch.deadline)) := by
      intro hbase1
      cases m with
      | tick dt => exact absurd rfl (hnotick dt)
      | land op => exact absurd rfl (hnoland op)
      | deliver ss' => exact hbase1
      | chain caller op =>
        rcases hbase1 with hf | ⟨t0, ho, hle⟩ | ⟨t0, ch, hst, hdis, hdd⟩
        · refine Or.inl ?_
          simp only [NetworkState.applyAdv]
          cases h : net1.chain.apply apps caller op with
          | none => simpa using hf
          | some s' => exact Adjudicator.finalizedWith_apply h hf
        · simp only [NetworkState.applyAdv]
          cases h : net1.chain.apply apps caller op with
          | none => exact Or.inr (Or.inl ⟨t0, ho, hle⟩)
          | some s' =>
            have hfo1 : net1.chain.finalOutcome c.address = none := by
              simp only [FixedPart.address_eq, Adjudicator.finalOutcome_channel, ho,
                ChannelStatus.finalOutcome_open]
            have hU : ∀ ss' ∈ op.proofStates, p ∈ ss'.signers →
                ∃ x ∈ net1.sent, x.state = ss'.state :=
              fun ss' hmem hsig => (hbounds.unforgeable net1 caller op hfeas ss' hmem).1 hsig
            cases op with
            | deposit a e x =>
              obtain ⟨-, -, -, -, hs, -⟩ := Adjudicator.deposit_some h
              refine Or.inr (Or.inl ⟨t0, ?_, hle⟩)
              rw [Adjudicator.statusOf_of_status hs]; exact ho
            | tick dt =>
              have hs' : net1.chain.tick dt = s' := by simpa using h
              subst hs'
              refine Or.inr (Or.inl ⟨t0, ?_, hle⟩)
              rw [Adjudicator.tick_statusOf]; exact ho
            | transfer a b =>
              by_cases hac : a = c
              · subst hac
                obtain ⟨o, -, -, hfo, -, -, -, -, -, -, -, -⟩ := Adjudicator.transfer_some h
                rw [hfo1] at hfo; exact absurd hfo (by simp)
              · obtain ⟨_, _, _, _, _, _, _, _, hs, _, _, _⟩ := Adjudicator.transfer_some h
                refine Or.inr (Or.inl ⟨t0, ?_, hle⟩)
                rw [Adjudicator.statusOf_of_status hs, Adjudicator.statusOf_setStatus,
                  if_neg (Ne.symm hac)]
                exact ho
            | reclaim l v =>
              by_cases hlc : l = c
              · subst hlc
                obtain ⟨oL, -, -, -, -, hfo, -, -, -, -, -, -, -, -⟩ := Adjudicator.reclaim_some h
                rw [hfo1] at hfo; exact absurd hfo (by simp)
              · obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hsr, _, _⟩ := Adjudicator.reclaim_some h
                refine Or.inr (Or.inl ⟨t0, ?_, hle⟩)
                rw [hsr, Adjudicator.statusOf_setStatus, if_neg (Ne.symm hlc)]
                exact ho
            | challenge c' proof cand =>
              by_cases hcc : c' = c
              · subst hcc
                obtain ⟨⟨-, hs, -, -⟩, rfl⟩ := Adjudicator.challenge_some h
                rcases hsupp proof cand hU hs with hlt | heqc
                · refine Or.inr (Or.inr ⟨cand.turnNum,
                    Challenge.mk cand (net1.chain.now + c'.challengeDuration), ?_, Or.inl hlt, ?_⟩)
                  · rw [Adjudicator.statusOf_setStatus, if_pos rfl]
                  · have hself : T.ε ≤ 2 * T.ε := by rw [Nat.two_mul]; exact Nat.le_add_left T.ε T.ε
                    have hge : T.ε ≤ c'.challengeDuration := le_trans hself hdur
                    exact lt_of_lt_of_le hεbound (Nat.add_le_add_left hge net1.chain.now)
                · refine Or.inr (Or.inr ⟨cand.turnNum,
                    Challenge.mk cand (net1.chain.now + c'.challengeDuration), ?_, Or.inr heqc, ?_⟩)
                  · rw [Adjudicator.statusOf_setStatus, if_pos rfl]
                  · have hself : T.ε ≤ 2 * T.ε := by rw [Nat.two_mul]; exact Nat.le_add_left T.ε T.ε
                    have hge : T.ε ≤ c'.challengeDuration := le_trans hself hdur
                    exact lt_of_lt_of_le hεbound (Nat.add_le_add_left hge net1.chain.now)
              · obtain ⟨-, rfl⟩ := Adjudicator.challenge_some h
                refine Or.inr (Or.inl ⟨t0, ?_, hle⟩)
                rw [Adjudicator.statusOf_setStatus, if_neg (Ne.symm hcc)]
                exact ho
            | checkpoint c' proof cand =>
              by_cases hcc : c' = c
              · subst hcc
                obtain ⟨⟨-, hs, -, -⟩, rfl⟩ := Adjudicator.checkpoint_some h
                refine Or.inr (Or.inl ⟨cand.turnNum, ?_, ?_⟩)
                · rw [Adjudicator.statusOf_setStatus, if_pos rfl]
                · rcases hsupp proof cand hU hs with hlt | heqc
                  · exact le_of_lt hlt
                  · exact le_of_eq (by rw [heqc])
              · obtain ⟨-, rfl⟩ := Adjudicator.checkpoint_some h
                refine Or.inr (Or.inl ⟨t0, ?_, hle⟩)
                rw [Adjudicator.statusOf_setStatus, if_neg (Ne.symm hcc)]
                exact ho
            | conclude c' ss' =>
              by_cases hcc : c' = c
              · subst hcc
                obtain ⟨⟨-, hproof'⟩, rfl⟩ := Adjudicator.conclude_some h
                refine Or.inl ?_
                have hp' : p ∈ ss'.signers := hproof'.2.2 p (hproof'.1 ▸ hp)
                have hmem : ss' ∈ (Op.conclude c' ss').proofStates := by simp [Op.proofStates]
                obtain ⟨x, hxmem, hxeq⟩ := hU ss' hmem hp'
                have hΩ' := hfinal x hxmem (hxeq ▸ hproof'.1) (hxeq ▸ hproof'.2.1)
                simp [Adjudicator.finalizedWith_channel, hxeq ▸ hΩ']
              · obtain ⟨-, rfl⟩ := Adjudicator.conclude_some h
                refine Or.inr (Or.inl ⟨t0, ?_, hle⟩)
                rw [Adjudicator.statusOf_setStatus, if_neg (Ne.symm hcc)]
                exact ho
        · have hmono : net1.chain.now ≤ D :=
            le_trans (le_trans (NetworkState.applyAdv_now_le apps net1 (.chain caller op))
              hrest.now_le) hDbound
          have hltdl : net1.chain.now < ch.deadline := lt_of_le_of_lt hmono hdd
          simp only [NetworkState.applyAdv]
          cases h : net1.chain.apply apps caller op with
          | none => exact Or.inr (Or.inr ⟨t0, ch, hst, hdis, hdd⟩)
          | some s' =>
            have hfo1 : net1.chain.finalOutcome c.address = none := by
              simp only [FixedPart.address_eq, Adjudicator.finalOutcome_channel, hst,
                ChannelStatus.finalOutcome_challenged, if_neg (not_le.mpr hltdl)]
            have hU : ∀ ss' ∈ op.proofStates, p ∈ ss'.signers →
                ∃ x ∈ net1.sent, x.state = ss'.state :=
              fun ss' hmem hsig => (hbounds.unforgeable net1 caller op hfeas ss' hmem).1 hsig
            cases op with
            | deposit a e x =>
              obtain ⟨-, -, -, -, hs, -⟩ := Adjudicator.deposit_some h
              refine Or.inr (Or.inr ⟨t0, ch, ?_, hdis, hdd⟩)
              rw [Adjudicator.statusOf_of_status hs]; exact hst
            | tick dt =>
              have hs' : net1.chain.tick dt = s' := by simpa using h
              subst hs'
              refine Or.inr (Or.inr ⟨t0, ch, ?_, hdis, hdd⟩)
              rw [Adjudicator.tick_statusOf]; exact hst
            | transfer a b =>
              by_cases hac : a = c
              · subst hac
                obtain ⟨o, -, -, hfo, -, -, -, -, -, -, -, -⟩ := Adjudicator.transfer_some h
                rw [hfo1] at hfo; exact absurd hfo (by simp)
              · obtain ⟨_, _, _, _, _, _, _, _, hs, _, _, _⟩ := Adjudicator.transfer_some h
                refine Or.inr (Or.inr ⟨t0, ch, ?_, hdis, hdd⟩)
                rw [Adjudicator.statusOf_of_status hs, Adjudicator.statusOf_setStatus,
                  if_neg (Ne.symm hac)]
                exact hst
            | reclaim l v =>
              by_cases hlc : l = c
              · subst hlc
                obtain ⟨oL, -, -, -, -, hfo, -, -, -, -, -, -, -, -⟩ := Adjudicator.reclaim_some h
                rw [hfo1] at hfo; exact absurd hfo (by simp)
              · obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hsr, _, _⟩ := Adjudicator.reclaim_some h
                refine Or.inr (Or.inr ⟨t0, ch, ?_, hdis, hdd⟩)
                rw [hsr, Adjudicator.statusOf_setStatus, if_neg (Ne.symm hlc)]
                exact hst
            | challenge c' proof cand =>
              by_cases hcc : c' = c
              · subst hcc
                obtain ⟨⟨-, hs, -, -⟩, rfl⟩ := Adjudicator.challenge_some h
                rcases hsupp proof cand hU hs with hlt | heqc
                · refine Or.inr (Or.inr ⟨cand.turnNum,
                    Challenge.mk cand (net1.chain.now + c'.challengeDuration), ?_, Or.inl hlt, ?_⟩)
                  · rw [Adjudicator.statusOf_setStatus, if_pos rfl]
                  · have hself : T.ε ≤ 2 * T.ε := by rw [Nat.two_mul]; exact Nat.le_add_left T.ε T.ε
                    have hge : T.ε ≤ c'.challengeDuration := le_trans hself hdur
                    exact lt_of_lt_of_le hεbound (Nat.add_le_add_left hge net1.chain.now)
                · refine Or.inr (Or.inr ⟨cand.turnNum,
                    Challenge.mk cand (net1.chain.now + c'.challengeDuration), ?_, Or.inr heqc, ?_⟩)
                  · rw [Adjudicator.statusOf_setStatus, if_pos rfl]
                  · have hself : T.ε ≤ 2 * T.ε := by rw [Nat.two_mul]; exact Nat.le_add_left T.ε T.ε
                    have hge : T.ε ≤ c'.challengeDuration := le_trans hself hdur
                    exact lt_of_lt_of_le hεbound (Nat.add_le_add_left hge net1.chain.now)
              · obtain ⟨-, rfl⟩ := Adjudicator.challenge_some h
                refine Or.inr (Or.inr ⟨t0, ch, ?_, hdis, hdd⟩)
                rw [Adjudicator.statusOf_setStatus, if_neg (Ne.symm hcc)]
                exact hst
            | checkpoint c' proof cand =>
              by_cases hcc : c' = c
              · subst hcc
                obtain ⟨⟨-, hs, -, -⟩, rfl⟩ := Adjudicator.checkpoint_some h
                refine Or.inr (Or.inl ⟨cand.turnNum, ?_, ?_⟩)
                · rw [Adjudicator.statusOf_setStatus, if_pos rfl]
                · rcases hsupp proof cand hU hs with hlt | heqc
                  · exact le_of_lt hlt
                  · exact le_of_eq (by rw [heqc])
              · obtain ⟨-, rfl⟩ := Adjudicator.checkpoint_some h
                refine Or.inr (Or.inr ⟨t0, ch, ?_, hdis, hdd⟩)
                rw [Adjudicator.statusOf_setStatus, if_neg (Ne.symm hcc)]
                exact hst
            | conclude c' ss' =>
              by_cases hcc : c' = c
              · subst hcc
                obtain ⟨⟨-, hproof'⟩, rfl⟩ := Adjudicator.conclude_some h
                refine Or.inl ?_
                have hp' : p ∈ ss'.signers := hproof'.2.2 p (hproof'.1 ▸ hp)
                have hmem : ss' ∈ (Op.conclude c' ss').proofStates := by simp [Op.proofStates]
                obtain ⟨x, hxmem, hxeq⟩ := hU ss' hmem hp'
                have hΩ' := hfinal x hxmem (hxeq ▸ hproof'.1) (hxeq ▸ hproof'.2.1)
                simp [Adjudicator.finalizedWith_channel, hxeq ▸ hΩ']
              · obtain ⟨-, rfl⟩ := Adjudicator.conclude_some h
                refine Or.inr (Or.inr ⟨t0, ch, ?_, hdis, hdd⟩)
                rw [Adjudicator.statusOf_setStatus, if_neg (Ne.symm hcc)]
                exact hst
    have hbase' := step hbase
    have hεbound' : D < (net1.applyAdv apps m).chain.now + T.ε :=
      lt_of_lt_of_le hεbound (Nat.add_le_add_right (NetworkState.applyAdv_now_le apps net1 m) T.ε)
    have hlatest' : ∀ t0 ∈ (net1.applyAdv apps m).sent, t0.state.channel = c →
        t0.state.turnNum < ss.state.turnNum ∨ t0.state = ss.state := by
      rw [NetworkState.applyAdv_sent]; exact hlatest
    have hfinal' : ∀ t0 ∈ (net1.applyAdv apps m).sent, t0.state.channel = c →
        t0.state.isFinal = true → t0.state.outcome = ss.state.outcome := by
      rw [NetworkState.applyAdv_sent]; exact hfinal
    exact ih hDbound hpnil hεbound' hlatest' hfinal' hbase'


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
    (hc : apps c.appDef = consensusRules) (hp : p ∈ c.participants)
    (hdur : 2 * T.ε ≤ c.challengeDuration) :
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
  intro net net' t hseq hDbound
  generalize hpnil : ([] : List (Op E)) = pending at hseq
  induction hseq with
  | nil => intro _ _ hbase; exact hbase
  | land hsplit _ _ => rw [← hpnil] at hsplit; simp at hsplit
  | @tick pending net1 net2 dt hfeas hgate hrest ih =>
    intro hlatest hfinal hbase
    have step : (net1.chain.finalizedWith c.address = some ss.state.outcome ∨
        ∃ T0 ch, net1.chain.statusOf c = .challenged T0 ch ∧ ss.state.turnNum ≤ T0 ∧
          ch.state = ss.state ∧ D < ch.deadline) →
        ((net1.applyAdv apps (AdvMove.tick dt)).chain.finalizedWith c.address =
          some ss.state.outcome ∨
        ∃ T0 ch, (net1.applyAdv apps (AdvMove.tick dt)).chain.statusOf c = .challenged T0 ch ∧
          ss.state.turnNum ≤ T0 ∧ ch.state = ss.state ∧ D < ch.deadline) := by
      intro hbase1
      rcases hbase1 with hf | ⟨T0, ch, hst, hT0, hchs, hdd⟩
      · exact Or.inl (by
          simpa [NetworkState.applyAdv, FixedPart.address_eq] using
            ChannelStatus.finalizedWith_mono (by simpa [FixedPart.address_eq] using hf)
              (Nat.le_add_right _ dt))
      · exact Or.inr ⟨T0, ch, by simpa [NetworkState.applyAdv] using hst, hT0, hchs, hdd⟩
    have hbase' := step hbase
    have hlatest' : ∀ t0 ∈ (net1.applyAdv apps (AdvMove.tick dt)).sent, t0.state.channel = c →
        t0.state.turnNum < ss.state.turnNum ∨ t0.state = ss.state := by
      rw [NetworkState.applyAdv_sent]; exact hlatest
    have hfinal' : ∀ t0 ∈ (net1.applyAdv apps (AdvMove.tick dt)).sent, t0.state.channel = c →
        t0.state.isFinal = true → t0.state.outcome = ss.state.outcome := by
      rw [NetworkState.applyAdv_sent]; exact hfinal
    exact ih hDbound hpnil hlatest' hfinal' hbase'
  | @other pending net1 net2 m hfeas hnotick hnoland hrest ih =>
    intro hlatest hfinal hbase
    have hsupp : ∀ (proof : SupportProof E) (cand : State E),
        (∀ ss' ∈ proof, p ∈ ss'.signers → ∃ x ∈ net1.sent, x.state = ss'.state) →
        (apps c.appDef).supports c proof cand = true →
        cand.turnNum < ss.state.turnNum ∨ cand = ss.state := by
      intro proof cand hU hs
      rw [hc] at hs
      match proof, hs with
      | [ss'], hs =>
        simp only [consensusRules, Bool.and_eq_true, decide_eq_true_eq] at hs
        obtain ⟨⟨hss', hch⟩, hall'⟩ := hs
        obtain ⟨x, hx, hxs⟩ := hU ss' (List.mem_singleton_self _) (hall' p (hch ▸ hp))
        have hb := hlatest x hx (by rw [hxs]; exact hch)
        rw [hxs, hss'] at hb
        exact hb
    have step : (net1.chain.finalizedWith c.address = some ss.state.outcome ∨
        ∃ T0 ch, net1.chain.statusOf c = .challenged T0 ch ∧ ss.state.turnNum ≤ T0 ∧
          ch.state = ss.state ∧ D < ch.deadline) →
        ((net1.applyAdv apps m).chain.finalizedWith c.address = some ss.state.outcome ∨
        ∃ T0 ch, (net1.applyAdv apps m).chain.statusOf c = .challenged T0 ch ∧
          ss.state.turnNum ≤ T0 ∧ ch.state = ss.state ∧ D < ch.deadline) := by
      intro hbase1
      cases m with
      | tick dt => exact absurd rfl (hnotick dt)
      | land op => exact absurd rfl (hnoland op)
      | deliver ss' => exact hbase1
      | chain caller op =>
        rcases hbase1 with hf | ⟨T0, ch, hst, hT0, hchs, hdd⟩
        · refine Or.inl ?_
          simp only [NetworkState.applyAdv]
          cases h : net1.chain.apply apps caller op with
          | none => simpa using hf
          | some s' => exact Adjudicator.finalizedWith_apply h hf
        · have hmono : net1.chain.now ≤ D :=
            le_trans (le_trans (NetworkState.applyAdv_now_le apps net1 (.chain caller op))
              hrest.now_le) hDbound
          have hltdl : net1.chain.now < ch.deadline := lt_of_le_of_lt hmono hdd
          have hm1 : net1.chain.mode c = .challenge := by
            rw [Adjudicator.mode_eq, hst, ChannelStatus.mode_challenged, if_neg (not_le.mpr hltdl)]
          simp only [NetworkState.applyAdv]
          cases h : net1.chain.apply apps caller op with
          | none => exact Or.inr ⟨T0, ch, hst, hT0, hchs, hdd⟩
          | some s' =>
            have hfo1 : net1.chain.finalOutcome c.address = none := by
              simp only [FixedPart.address_eq, Adjudicator.finalOutcome_channel, hst,
                ChannelStatus.finalOutcome_challenged, if_neg (not_le.mpr hltdl)]
            have hU : ∀ ss' ∈ op.proofStates, p ∈ ss'.signers →
                ∃ x ∈ net1.sent, x.state = ss'.state :=
              fun ss' hmem hsig => (hbounds.unforgeable net1 caller op hfeas ss' hmem).1 hsig
            cases op with
            | deposit a e x =>
              obtain ⟨-, -, -, -, hs, -⟩ := Adjudicator.deposit_some h
              exact Or.inr ⟨T0, ch, by rw [Adjudicator.statusOf_of_status hs]; exact hst, hT0,
                hchs, hdd⟩
            | tick dt =>
              have hs' : net1.chain.tick dt = s' := by simpa using h
              subst hs'
              exact Or.inr ⟨T0, ch, by rw [Adjudicator.tick_statusOf]; exact hst, hT0, hchs, hdd⟩
            | transfer a b =>
              by_cases hac : a = c
              · subst hac
                obtain ⟨o, -, -, hfo, -, -, -, -, -, -, -, -⟩ := Adjudicator.transfer_some h
                rw [hfo1] at hfo; exact absurd hfo (by simp)
              · obtain ⟨_, _, _, _, _, _, _, _, hs, _, _, _⟩ := Adjudicator.transfer_some h
                exact Or.inr ⟨T0, ch, by
                  rw [Adjudicator.statusOf_of_status hs, Adjudicator.statusOf_setStatus,
                    if_neg (Ne.symm hac)]; exact hst, hT0, hchs, hdd⟩
            | reclaim l v =>
              by_cases hlc : l = c
              · subst hlc
                obtain ⟨oL, -, -, -, -, hfo, -, -, -, -, -, -, -, -⟩ := Adjudicator.reclaim_some h
                rw [hfo1] at hfo; exact absurd hfo (by simp)
              · obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hsr, _, _⟩ := Adjudicator.reclaim_some h
                exact Or.inr ⟨T0, ch, by
                  rw [hsr, Adjudicator.statusOf_setStatus, if_neg (Ne.symm hlc)]; exact hst, hT0,
                  hchs, hdd⟩
            | challenge c' proof cand =>
              by_cases hcc : c' = c
              · exfalso; subst hcc
                obtain ⟨⟨-, hs, -, hmode⟩, -⟩ := Adjudicator.challenge_some h
                rcases hmode with ⟨hmo, -⟩ | ⟨-, hlt2⟩
                · rw [hm1] at hmo; exact absurd hmo (by decide)
                · rw [hst, ChannelStatus.turnNumRecord_challenged] at hlt2
                  rcases hsupp proof cand hU hs with hlt3 | heqc3
                  · omega
                  · rw [heqc3] at hlt2; omega
              · obtain ⟨-, rfl⟩ := Adjudicator.challenge_some h
                exact Or.inr ⟨T0, ch, by
                  rw [Adjudicator.statusOf_setStatus, if_neg (Ne.symm hcc)]; exact hst, hT0, hchs,
                  hdd⟩
            | checkpoint c' proof cand =>
              by_cases hcc : c' = c
              · exfalso; subst hcc
                obtain ⟨⟨-, hs, -, hlt2⟩, -⟩ := Adjudicator.checkpoint_some h
                rw [hst, ChannelStatus.turnNumRecord_challenged] at hlt2
                rcases hsupp proof cand hU hs with hlt3 | heqc3
                · omega
                · rw [heqc3] at hlt2; omega
              · obtain ⟨-, rfl⟩ := Adjudicator.checkpoint_some h
                exact Or.inr ⟨T0, ch, by
                  rw [Adjudicator.statusOf_setStatus, if_neg (Ne.symm hcc)]; exact hst, hT0, hchs,
                  hdd⟩
            | conclude c' ss' =>
              by_cases hcc : c' = c
              · subst hcc
                obtain ⟨⟨-, hproof'⟩, rfl⟩ := Adjudicator.conclude_some h
                refine Or.inl ?_
                have hp' : p ∈ ss'.signers := hproof'.2.2 p (hproof'.1 ▸ hp)
                have hmem : ss' ∈ (Op.conclude c' ss').proofStates := by simp [Op.proofStates]
                obtain ⟨x, hxmem, hxeq⟩ := hU ss' hmem hp'
                have hΩ' := hfinal x hxmem (hxeq ▸ hproof'.1) (hxeq ▸ hproof'.2.1)
                simp [Adjudicator.finalizedWith_channel, hxeq ▸ hΩ']
              · obtain ⟨-, rfl⟩ := Adjudicator.conclude_some h
                exact Or.inr ⟨T0, ch, by
                  rw [Adjudicator.statusOf_setStatus, if_neg (Ne.symm hcc)]; exact hst, hT0, hchs,
                  hdd⟩
    have hbase' := step hbase
    have hlatest' : ∀ t0 ∈ (net1.applyAdv apps m).sent, t0.state.channel = c →
        t0.state.turnNum < ss.state.turnNum ∨ t0.state = ss.state := by
      rw [NetworkState.applyAdv_sent]; exact hlatest
    have hfinal' : ∀ t0 ∈ (net1.applyAdv apps m).sent, t0.state.channel = c →
        t0.state.isFinal = true → t0.state.outcome = ss.state.outcome := by
      rw [NetworkState.applyAdv_sent]; exact hfinal
    exact ih hDbound hpnil hlatest' hfinal' hbase'
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
  | none => simp
  | some s' =>
    obtain ⟨-, rfl⟩ := Adjudicator.challenge_some h
    exact ⟨by simp [Adjudicator.statusOf_setStatus, if_neg (Ne.symm hne)],
      by simp [FixedPart.address_eq, Adjudicator.finalizedWith_channel,
        Adjudicator.statusOf_setStatus, if_neg (Ne.symm hne)]⟩

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
    {c : FixedPart} {ss : SignedState E}
    (hc : apps c.appDef = consensusRules) (hp : p ∈ c.participants) (hall : ss.ByAll)
    (hchan : ss.state.channel = c) (hdur : 2 * T.ε ≤ c.challengeDuration)
    {net1 net' : NetworkState E p}
    (hεbound : net'.chain.now < net1.chain.now + T.ε)
    (hmono0 : net1.chain.now ≤ net'.chain.now)
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
      simpa [FixedPart.address_eq, Adjudicator.finalizedWith_channel] using hf
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
      refine ⟨hp, by rw [hc]; simp [consensusRules, hchan, hall], hchan, Or.inl ⟨?_, ?_⟩⟩
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
      have hge : T.ε ≤ c.challengeDuration := le_trans hself hdur
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
        refine ⟨hp, by rw [hc]; simp [consensusRules, hchan, hall], hchan,
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
        have hge : T.ε ≤ c.challengeDuration := le_trans hself hdur
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
    local one — the fix this ruling's own argument turns on
    (`Strategy.lean`'s header, "Time bounds per pending action"). -/
theorem latest_round_keeps_status_two_ordered {apps : Apps E} {p : Participant} {T : Threat E p}
    (hbounds : Bounds apps p T)
    {c1 c2 : FixedPart} {ss1 ss2 : SignedState E} (hne : c1 ≠ c2)
    (hc1 : apps c1.appDef = consensusRules) (hc2 : apps c2.appDef = consensusRules)
    (hp1 : p ∈ c1.participants) (hp2 : p ∈ c2.participants)
    (hall1 : ss1.ByAll) (hchan1 : ss1.state.channel = c1)
    (hall2 : ss2.ByAll) (hchan2 : ss2.state.channel = c2)
    (hdur1 : 2 * T.ε ≤ c1.challengeDuration) (hdur2 : 2 * T.ε ≤ c2.challengeDuration)
    {net n1 net' : NetworkState E p} {t : Time}
    (hpre : Threat.RoundSeq apps T t [] net n1)
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
  have hbase2_n1 := latest_round_keeps_status_nil_prelanding hbounds hc2 hp2 hdur2
    (D := net'.chain.now) hpre hmono_n1 hεbound hlatest2 hfinal2 hbase2
  -- `c1`'s pre-land invariant, carried unaffected to `n1`.
  have hbase1_n1 := latest_round_keeps_status_nil_prelanding hbounds hc1 hp1 hdur1
    (D := net'.chain.now) hpre hmono_n1 hεbound hlatest1 hfinal1 hbase1
  -- `c1` lands at `n1`.
  have hc1_landed := land_own_challenge_transitions_status hc1 hp1 hall1 hchan1 hdur1
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
  have hc1_n2 := latest_round_keeps_status_nil_D hbounds hc1 hp1 hdur1
    (D := net'.chain.now) hmid_pre hmono_n2 (by rw [hnet1'_sent]; exact hlatest1)
    (by rw [hnet1'_sent]; exact hfinal1) hc1_landed
  -- `c2`'s pre-land invariant, carried unaffected through the same phase.
  have hbase2_n2 := latest_round_keeps_status_nil_prelanding hbounds hc2 hp2 hdur2
    (D := net'.chain.now) hmid_pre hmono_n2 hεbound_n1' (by rw [hnet1'_sent]; exact hlatest2)
    (by rw [hnet1'_sent]; exact hfinal2) hbase2_landed
  -- `c2` lands at `n2`.
  have hc2_landed := land_own_challenge_transitions_status hc2 hp2 hall2 hchan2 hdur2
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
  have hc1_final := latest_round_keeps_status_nil_D hbounds hc1 hp1 hdur1
    (D := net'.chain.now) hmid_post (le_refl _)
    (by rw [hn2'_sent]; exact hlatest1) (by rw [hn2'_sent]; exact hfinal1) hc1_landed2
  have hc2_final := latest_round_keeps_status_nil_D hbounds hc2 hp2 hdur2
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
    (hbounds : Bounds apps p T)
    {c1 c2 : FixedPart} {ss1 ss2 : SignedState E} (hne : c1 ≠ c2)
    (hc1 : apps c1.appDef = consensusRules) (hc2 : apps c2.appDef = consensusRules)
    (hp1 : p ∈ c1.participants) (hp2 : p ∈ c2.participants)
    (hall1 : ss1.ByAll) (hchan1 : ss1.state.channel = c1)
    (hall2 : ss2.ByAll) (hchan2 : ss2.state.channel = c2)
    (hdur1 : 2 * T.ε ≤ c1.challengeDuration) (hdur2 : 2 * T.ε ≤ c2.challengeDuration)
    {net net' : NetworkState E p} (t : Time) (ht : t = net.chain.now)
    (hseq : Threat.RoundSeq apps T t
      [Op.challenge c1 [ss1] ss1.state, Op.challenge c2 [ss2] ss2.state] net net') :
    net'.chain.now < net.chain.now + T.ε →
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
  clear ht
  intro hεbound hlatest1 hlatest2 hfinal1 hfinal2 hbase1 hbase2
  rcases hseq.peel_two with ⟨n1, hpre, hmid⟩ | ⟨n1, hpre, hmid⟩
  · exact latest_round_keeps_status_two_ordered hbounds hne hc1 hc2 hp1 hp2 hall1 hchan1 hall2
      hchan2 hdur1 hdur2 hpre hmid hεbound hlatest1 hlatest2 hfinal1 hfinal2 hbase1 hbase2
  · have hswap := latest_round_keeps_status_two_ordered hbounds hne.symm hc2 hc1 hp2 hp1 hall2
      hchan2 hall1 hchan1 hdur2 hdur1 hpre hmid hεbound hlatest2 hlatest1 hfinal2 hfinal1 hbase2
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
  generalize heq : ([Op.challenge c [ss] ss.state] : List (Op E)) = pending at hseq
  induction hseq with
  | nil => cases heq
  | @land pending net1 net2 op l1 l2 hsplit hrest ih =>
    intro hεbound hlatest hfinal hbase
    cases heq
    rcases l1 with _ | ⟨a, l1⟩
    · rcases l2 with _ | ⟨b, l2⟩
      · simp only [List.nil_append, List.cons.injEq] at hsplit
        obtain ⟨hopeq, -⟩ := hsplit
        subst hopeq
        have hbase_land :
            (net1.applyAdv apps (AdvMove.land (Op.challenge c [ss] ss.state))).chain.finalizedWith
              c.address = some ss.state.outcome ∨
            ∃ T0 ch,
              (net1.applyAdv apps (AdvMove.land (Op.challenge c [ss] ss.state))).chain.statusOf c =
                .challenged T0 ch ∧ ss.state.turnNum ≤ T0 ∧ ch.state = ss.state ∧
              net2.chain.now < ch.deadline := by
          rcases hbase with hf | ⟨t0, ho, hle⟩ | ⟨t0, ch0, hst0, hdis0, hdd0⟩
          · have hfz1 : (net1.chain.statusOf c).finalizedWith net1.chain.now =
                some ss.state.outcome := by
              simpa [FixedPart.address_eq, Adjudicator.finalizedWith_channel] using hf
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
              refine ⟨hp, by rw [hc]; simp [consensusRules, hchan, hall], hchan, Or.inl ⟨?_, ?_⟩⟩
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
              have hge : T.ε ≤ c.challengeDuration := le_trans hself hdur
              exact lt_of_lt_of_le hεbound (Nat.add_le_add_left hge net1.chain.now)
          · have hmono0 : net1.chain.now ≤ net2.chain.now :=
              le_trans
                (NetworkState.applyAdv_now_le apps net1 (.land (Op.challenge c [ss] ss.state)))
                hrest.now_le
            have hltdl0 : net1.chain.now < ch0.deadline := lt_of_le_of_lt hmono0 hdd0
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
                refine ⟨hp, by rw [hc]; simp [consensusRules, hchan, hall], hchan,
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
                have hge : T.ε ≤ c.challengeDuration := le_trans hself hdur
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
        have hεbound' : net2.chain.now <
            (net1.applyAdv apps (AdvMove.land (Op.challenge c [ss] ss.state))).chain.now + T.ε :=
          lt_of_lt_of_le hεbound
            (Nat.add_le_add_right
              (NetworkState.applyAdv_now_le apps net1 (.land (Op.challenge c [ss] ss.state))) T.ε)
        have hlatest_land : ∀ t0 ∈
            (net1.applyAdv apps (AdvMove.land (Op.challenge c [ss] ss.state))).sent,
            t0.state.channel = c → t0.state.turnNum < ss.state.turnNum ∨ t0.state = ss.state := by
          rw [NetworkState.applyAdv_sent]; exact hlatest
        have hfinal_land : ∀ t0 ∈
            (net1.applyAdv apps (AdvMove.land (Op.challenge c [ss] ss.state))).sent,
            t0.state.channel = c → t0.state.isFinal = true →
            t0.state.outcome = ss.state.outcome := by
          rw [NetworkState.applyAdv_sent]; exact hfinal
        exact latest_round_keeps_status_nil hbounds hc hp hdur hrest hεbound' hlatest_land
          hfinal_land hbase_land
      · simp at hsplit
    · simp at hsplit
  | @tick pending net1 net2 dt hfeas hgate hrest ih =>
    intro hεbound hlatest hfinal hbase
    have step : (net1.chain.finalizedWith c.address = some ss.state.outcome ∨
        (∃ t0, net1.chain.statusOf c = .open t0 ∧ t0 ≤ ss.state.turnNum) ∨
        (∃ t0 ch, net1.chain.statusOf c = .challenged t0 ch ∧
          (t0 < ss.state.turnNum ∨ ch.state = ss.state) ∧ net2.chain.now < ch.deadline)) →
        ((net1.applyAdv apps (AdvMove.tick dt)).chain.finalizedWith c.address =
          some ss.state.outcome ∨
        (∃ t0, (net1.applyAdv apps (AdvMove.tick dt)).chain.statusOf c = .open t0 ∧
          t0 ≤ ss.state.turnNum) ∨
        (∃ t0 ch, (net1.applyAdv apps (AdvMove.tick dt)).chain.statusOf c = .challenged t0 ch ∧
          (t0 < ss.state.turnNum ∨ ch.state = ss.state) ∧ net2.chain.now < ch.deadline)) := by
      intro hbase1
      rcases hbase1 with hf | ⟨t0, ho, hle⟩ | ⟨t0, ch, hst, hdis, hdd⟩
      · exact Or.inl (by
          simpa [NetworkState.applyAdv, FixedPart.address_eq] using
            ChannelStatus.finalizedWith_mono (by simpa [FixedPart.address_eq] using hf)
              (Nat.le_add_right _ dt))
      · exact Or.inr (Or.inl ⟨t0, by simpa [NetworkState.applyAdv] using ho, hle⟩)
      · exact Or.inr (Or.inr ⟨t0, ch, by simpa [NetworkState.applyAdv] using hst, hdis, hdd⟩)
    have hbase' := step hbase
    have hεbound' : net2.chain.now < (net1.applyAdv apps (AdvMove.tick dt)).chain.now + T.ε :=
      lt_of_lt_of_le hεbound
        (Nat.add_le_add_right (NetworkState.applyAdv_now_le apps net1 (.tick dt)) T.ε)
    have hlatest' : ∀ t0 ∈ (net1.applyAdv apps (AdvMove.tick dt)).sent, t0.state.channel = c →
        t0.state.turnNum < ss.state.turnNum ∨ t0.state = ss.state := by
      rw [NetworkState.applyAdv_sent]; exact hlatest
    have hfinal' : ∀ t0 ∈ (net1.applyAdv apps (AdvMove.tick dt)).sent, t0.state.channel = c →
        t0.state.isFinal = true → t0.state.outcome = ss.state.outcome := by
      rw [NetworkState.applyAdv_sent]; exact hfinal
    exact ih heq hεbound' hlatest' hfinal' hbase'
  | @other pending net1 net2 m hfeas hnotick hnoland hrest ih =>
    intro hεbound hlatest hfinal hbase
    have hsupp : ∀ (proof : SupportProof E) (cand : State E),
        (∀ ss' ∈ proof, p ∈ ss'.signers → ∃ x ∈ net1.sent, x.state = ss'.state) →
        (apps c.appDef).supports c proof cand = true →
        cand.turnNum < ss.state.turnNum ∨ cand = ss.state := by
      intro proof cand hU hs
      rw [hc] at hs
      match proof, hs with
      | [ss'], hs =>
        simp only [consensusRules, Bool.and_eq_true, decide_eq_true_eq] at hs
        obtain ⟨⟨hss', hch⟩, hall'⟩ := hs
        obtain ⟨x, hx, hxs⟩ := hU ss' (List.mem_singleton_self _) (hall' p (hch ▸ hp))
        have hb := hlatest x hx (by rw [hxs]; exact hch)
        rw [hxs, hss'] at hb
        exact hb
    have step : (net1.chain.finalizedWith c.address = some ss.state.outcome ∨
        (∃ t0, net1.chain.statusOf c = .open t0 ∧ t0 ≤ ss.state.turnNum) ∨
        (∃ t0 ch, net1.chain.statusOf c = .challenged t0 ch ∧
          (t0 < ss.state.turnNum ∨ ch.state = ss.state) ∧ net2.chain.now < ch.deadline)) →
        ((net1.applyAdv apps m).chain.finalizedWith c.address = some ss.state.outcome ∨
        (∃ t0, (net1.applyAdv apps m).chain.statusOf c = .open t0 ∧ t0 ≤ ss.state.turnNum) ∨
        (∃ t0 ch, (net1.applyAdv apps m).chain.statusOf c = .challenged t0 ch ∧
          (t0 < ss.state.turnNum ∨ ch.state = ss.state) ∧ net2.chain.now < ch.deadline)) := by
      intro hbase1
      cases m with
      | tick dt => exact absurd rfl (hnotick dt)
      | land op => exact absurd rfl (hnoland op)
      | deliver ss' => exact hbase1
      | chain caller op =>
        rcases hbase1 with hf | ⟨t0, ho, hle⟩ | ⟨t0, ch, hst, hdis, hdd⟩
        · refine Or.inl ?_
          simp only [NetworkState.applyAdv]
          cases h : net1.chain.apply apps caller op with
          | none => simpa using hf
          | some s' => exact Adjudicator.finalizedWith_apply h hf
        · simp only [NetworkState.applyAdv]
          cases h : net1.chain.apply apps caller op with
          | none => exact Or.inr (Or.inl ⟨t0, ho, hle⟩)
          | some s' =>
            have hfo1 : net1.chain.finalOutcome c.address = none := by
              simp only [FixedPart.address_eq, Adjudicator.finalOutcome_channel, ho,
                ChannelStatus.finalOutcome_open]
            have hU : ∀ ss' ∈ op.proofStates, p ∈ ss'.signers →
                ∃ x ∈ net1.sent, x.state = ss'.state :=
              fun ss' hmem hsig => (hbounds.unforgeable net1 caller op hfeas ss' hmem).1 hsig
            cases op with
            | deposit a e x =>
              obtain ⟨-, -, -, -, hs, -⟩ := Adjudicator.deposit_some h
              refine Or.inr (Or.inl ⟨t0, ?_, hle⟩)
              rw [Adjudicator.statusOf_of_status hs]; exact ho
            | tick dt =>
              have hs' : net1.chain.tick dt = s' := by simpa using h
              subst hs'
              refine Or.inr (Or.inl ⟨t0, ?_, hle⟩)
              rw [Adjudicator.tick_statusOf]; exact ho
            | transfer a b =>
              by_cases hac : a = c
              · subst hac
                obtain ⟨o, -, -, hfo, -, -, -, -, -, -, -, -⟩ := Adjudicator.transfer_some h
                rw [hfo1] at hfo; exact absurd hfo (by simp)
              · obtain ⟨_, _, _, _, _, _, _, _, hs, _, _, _⟩ := Adjudicator.transfer_some h
                refine Or.inr (Or.inl ⟨t0, ?_, hle⟩)
                rw [Adjudicator.statusOf_of_status hs, Adjudicator.statusOf_setStatus,
                  if_neg (Ne.symm hac)]
                exact ho
            | reclaim l v =>
              by_cases hlc : l = c
              · subst hlc
                obtain ⟨oL, -, -, -, -, hfo, -, -, -, -, -, -, -, -⟩ := Adjudicator.reclaim_some h
                rw [hfo1] at hfo; exact absurd hfo (by simp)
              · obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hsr, _, _⟩ := Adjudicator.reclaim_some h
                refine Or.inr (Or.inl ⟨t0, ?_, hle⟩)
                rw [hsr, Adjudicator.statusOf_setStatus, if_neg (Ne.symm hlc)]
                exact ho
            | challenge c' proof cand =>
              by_cases hcc : c' = c
              · subst hcc
                obtain ⟨⟨-, hs, -, -⟩, rfl⟩ := Adjudicator.challenge_some h
                rcases hsupp proof cand hU hs with hlt | heqc
                · refine Or.inr (Or.inr ⟨cand.turnNum,
                    Challenge.mk cand (net1.chain.now + c'.challengeDuration), ?_, Or.inl hlt, ?_⟩)
                  · rw [Adjudicator.statusOf_setStatus, if_pos rfl]
                  · have hself : T.ε ≤ 2 * T.ε := by rw [Nat.two_mul]; exact Nat.le_add_left T.ε T.ε
                    have hge : T.ε ≤ c'.challengeDuration := le_trans hself hdur
                    exact lt_of_lt_of_le hεbound (Nat.add_le_add_left hge net1.chain.now)
                · refine Or.inr (Or.inr ⟨cand.turnNum,
                    Challenge.mk cand (net1.chain.now + c'.challengeDuration), ?_, Or.inr heqc, ?_⟩)
                  · rw [Adjudicator.statusOf_setStatus, if_pos rfl]
                  · have hself : T.ε ≤ 2 * T.ε := by rw [Nat.two_mul]; exact Nat.le_add_left T.ε T.ε
                    have hge : T.ε ≤ c'.challengeDuration := le_trans hself hdur
                    exact lt_of_lt_of_le hεbound (Nat.add_le_add_left hge net1.chain.now)
              · obtain ⟨-, rfl⟩ := Adjudicator.challenge_some h
                refine Or.inr (Or.inl ⟨t0, ?_, hle⟩)
                rw [Adjudicator.statusOf_setStatus, if_neg (Ne.symm hcc)]
                exact ho
            | checkpoint c' proof cand =>
              by_cases hcc : c' = c
              · subst hcc
                obtain ⟨⟨-, hs, -, -⟩, rfl⟩ := Adjudicator.checkpoint_some h
                refine Or.inr (Or.inl ⟨cand.turnNum, ?_, ?_⟩)
                · rw [Adjudicator.statusOf_setStatus, if_pos rfl]
                · rcases hsupp proof cand hU hs with hlt | heqc
                  · exact le_of_lt hlt
                  · exact le_of_eq (by rw [heqc])
              · obtain ⟨-, rfl⟩ := Adjudicator.checkpoint_some h
                refine Or.inr (Or.inl ⟨t0, ?_, hle⟩)
                rw [Adjudicator.statusOf_setStatus, if_neg (Ne.symm hcc)]
                exact ho
            | conclude c' ss' =>
              by_cases hcc : c' = c
              · subst hcc
                obtain ⟨⟨-, hproof'⟩, rfl⟩ := Adjudicator.conclude_some h
                refine Or.inl ?_
                have hp' : p ∈ ss'.signers := hproof'.2.2 p (hproof'.1 ▸ hp)
                have hmem : ss' ∈ (Op.conclude c' ss').proofStates := by simp [Op.proofStates]
                obtain ⟨x, hxmem, hxeq⟩ := hU ss' hmem hp'
                have hΩ' := hfinal x hxmem (hxeq ▸ hproof'.1) (hxeq ▸ hproof'.2.1)
                simp [Adjudicator.finalizedWith_channel, hxeq ▸ hΩ']
              · obtain ⟨-, rfl⟩ := Adjudicator.conclude_some h
                refine Or.inr (Or.inl ⟨t0, ?_, hle⟩)
                rw [Adjudicator.statusOf_setStatus, if_neg (Ne.symm hcc)]
                exact ho
        · have hmono : net1.chain.now ≤ net2.chain.now :=
            le_trans (NetworkState.applyAdv_now_le apps net1 (.chain caller op)) hrest.now_le
          have hltdl : net1.chain.now < ch.deadline := lt_of_le_of_lt hmono hdd
          simp only [NetworkState.applyAdv]
          cases h : net1.chain.apply apps caller op with
          | none => exact Or.inr (Or.inr ⟨t0, ch, hst, hdis, hdd⟩)
          | some s' =>
            have hfo1 : net1.chain.finalOutcome c.address = none := by
              simp only [FixedPart.address_eq, Adjudicator.finalOutcome_channel, hst,
                ChannelStatus.finalOutcome_challenged, if_neg (not_le.mpr hltdl)]
            have hU : ∀ ss' ∈ op.proofStates, p ∈ ss'.signers →
                ∃ x ∈ net1.sent, x.state = ss'.state :=
              fun ss' hmem hsig => (hbounds.unforgeable net1 caller op hfeas ss' hmem).1 hsig
            cases op with
            | deposit a e x =>
              obtain ⟨-, -, -, -, hs, -⟩ := Adjudicator.deposit_some h
              refine Or.inr (Or.inr ⟨t0, ch, ?_, hdis, hdd⟩)
              rw [Adjudicator.statusOf_of_status hs]; exact hst
            | tick dt =>
              have hs' : net1.chain.tick dt = s' := by simpa using h
              subst hs'
              refine Or.inr (Or.inr ⟨t0, ch, ?_, hdis, hdd⟩)
              rw [Adjudicator.tick_statusOf]; exact hst
            | transfer a b =>
              by_cases hac : a = c
              · subst hac
                obtain ⟨o, -, -, hfo, -, -, -, -, -, -, -, -⟩ := Adjudicator.transfer_some h
                rw [hfo1] at hfo; exact absurd hfo (by simp)
              · obtain ⟨_, _, _, _, _, _, _, _, hs, _, _, _⟩ := Adjudicator.transfer_some h
                refine Or.inr (Or.inr ⟨t0, ch, ?_, hdis, hdd⟩)
                rw [Adjudicator.statusOf_of_status hs, Adjudicator.statusOf_setStatus,
                  if_neg (Ne.symm hac)]
                exact hst
            | reclaim l v =>
              by_cases hlc : l = c
              · subst hlc
                obtain ⟨oL, -, -, -, -, hfo, -, -, -, -, -, -, -, -⟩ := Adjudicator.reclaim_some h
                rw [hfo1] at hfo; exact absurd hfo (by simp)
              · obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hsr, _, _⟩ := Adjudicator.reclaim_some h
                refine Or.inr (Or.inr ⟨t0, ch, ?_, hdis, hdd⟩)
                rw [hsr, Adjudicator.statusOf_setStatus, if_neg (Ne.symm hlc)]
                exact hst
            | challenge c' proof cand =>
              by_cases hcc : c' = c
              · subst hcc
                obtain ⟨⟨-, hs, -, -⟩, rfl⟩ := Adjudicator.challenge_some h
                rcases hsupp proof cand hU hs with hlt | heqc
                · refine Or.inr (Or.inr ⟨cand.turnNum,
                    Challenge.mk cand (net1.chain.now + c'.challengeDuration), ?_, Or.inl hlt, ?_⟩)
                  · rw [Adjudicator.statusOf_setStatus, if_pos rfl]
                  · have hself : T.ε ≤ 2 * T.ε := by rw [Nat.two_mul]; exact Nat.le_add_left T.ε T.ε
                    have hge : T.ε ≤ c'.challengeDuration := le_trans hself hdur
                    exact lt_of_lt_of_le hεbound (Nat.add_le_add_left hge net1.chain.now)
                · refine Or.inr (Or.inr ⟨cand.turnNum,
                    Challenge.mk cand (net1.chain.now + c'.challengeDuration), ?_, Or.inr heqc, ?_⟩)
                  · rw [Adjudicator.statusOf_setStatus, if_pos rfl]
                  · have hself : T.ε ≤ 2 * T.ε := by rw [Nat.two_mul]; exact Nat.le_add_left T.ε T.ε
                    have hge : T.ε ≤ c'.challengeDuration := le_trans hself hdur
                    exact lt_of_lt_of_le hεbound (Nat.add_le_add_left hge net1.chain.now)
              · obtain ⟨-, rfl⟩ := Adjudicator.challenge_some h
                refine Or.inr (Or.inr ⟨t0, ch, ?_, hdis, hdd⟩)
                rw [Adjudicator.statusOf_setStatus, if_neg (Ne.symm hcc)]
                exact hst
            | checkpoint c' proof cand =>
              by_cases hcc : c' = c
              · subst hcc
                obtain ⟨⟨-, hs, -, -⟩, rfl⟩ := Adjudicator.checkpoint_some h
                refine Or.inr (Or.inl ⟨cand.turnNum, ?_, ?_⟩)
                · rw [Adjudicator.statusOf_setStatus, if_pos rfl]
                · rcases hsupp proof cand hU hs with hlt | heqc
                  · exact le_of_lt hlt
                  · exact le_of_eq (by rw [heqc])
              · obtain ⟨-, rfl⟩ := Adjudicator.checkpoint_some h
                refine Or.inr (Or.inr ⟨t0, ch, ?_, hdis, hdd⟩)
                rw [Adjudicator.statusOf_setStatus, if_neg (Ne.symm hcc)]
                exact hst
            | conclude c' ss' =>
              by_cases hcc : c' = c
              · subst hcc
                obtain ⟨⟨-, hproof'⟩, rfl⟩ := Adjudicator.conclude_some h
                refine Or.inl ?_
                have hp' : p ∈ ss'.signers := hproof'.2.2 p (hproof'.1 ▸ hp)
                have hmem : ss' ∈ (Op.conclude c' ss').proofStates := by simp [Op.proofStates]
                obtain ⟨x, hxmem, hxeq⟩ := hU ss' hmem hp'
                have hΩ' := hfinal x hxmem (hxeq ▸ hproof'.1) (hxeq ▸ hproof'.2.1)
                simp [Adjudicator.finalizedWith_channel, hxeq ▸ hΩ']
              · obtain ⟨-, rfl⟩ := Adjudicator.conclude_some h
                refine Or.inr (Or.inr ⟨t0, ch, ?_, hdis, hdd⟩)
                rw [Adjudicator.statusOf_setStatus, if_neg (Ne.symm hcc)]
                exact hst
    have hbase' := step hbase
    have hεbound' : net2.chain.now < (net1.applyAdv apps m).chain.now + T.ε :=
      lt_of_lt_of_le hεbound (Nat.add_le_add_right (NetworkState.applyAdv_now_le apps net1 m) T.ε)
    have hlatest' : ∀ t0 ∈ (net1.applyAdv apps m).sent, t0.state.channel = c →
        t0.state.turnNum < ss.state.turnNum ∨ t0.state = ss.state := by
      rw [NetworkState.applyAdv_sent]; exact hlatest
    have hfinal' : ∀ t0 ∈ (net1.applyAdv apps m).sent, t0.state.channel = c →
        t0.state.isFinal = true → t0.state.outcome = ss.state.outcome := by
      rw [NetworkState.applyAdv_sent]; exact hfinal
    exact ih heq hεbound' hlatest' hfinal' hbase'

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
    (hc : apps c.appDef = consensusRules) (hp : p ∈ c.participants) (hchs : ch.state = ss.state)
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
  | land hsplit _ _ => rw [← hpnil] at hsplit; simp at hsplit
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
        · exact Or.inr (by simpa [NetworkState.applyAdv] using hst)
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
      rw [hc] at hs
      match proof, hs with
      | [ss'], hs =>
        simp only [consensusRules, Bool.and_eq_true, decide_eq_true_eq] at hs
        obtain ⟨⟨hss', hch⟩, hall'⟩ := hs
        obtain ⟨x, hx, hxs⟩ := hU ss' (List.mem_singleton_self _) (hall' p (hch ▸ hp))
        have hb := hlatest x hx (by rw [hxs]; exact hch)
        rw [hxs, hss'] at hb
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
          | none => simpa using hf
          | some s' => exact Adjudicator.finalizedWith_apply h hf
        · by_cases hexp : ch.deadline ≤ net1.chain.now
          · have hf : net1.chain.finalizedWith c.address = some ss.state.outcome := by
              simp only [FixedPart.address_eq, Adjudicator.finalizedWith_channel, hst,
                ChannelStatus.finalizedWith_challenged, if_pos hexp, hchs]
            refine Or.inl ?_
            simp only [NetworkState.applyAdv]
            cases h : net1.chain.apply apps caller op with
            | none => simpa using hf
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
                have hs' : net1.chain.tick dt = s' := by simpa using h
                subst hs'
                refine Or.inr ?_
                rw [Adjudicator.tick_statusOf]; exact hst
              | transfer a b =>
                by_cases hac : a = c
                · subst hac
                  obtain ⟨o, -, -, hfo, -, -, -, -, -, -, -, -⟩ := Adjudicator.transfer_some h
                  rw [hfo1] at hfo; exact absurd hfo (by simp)
                · obtain ⟨_, _, _, _, _, _, _, _, hs, _, _, _⟩ := Adjudicator.transfer_some h
                  refine Or.inr ?_
                  rw [Adjudicator.statusOf_of_status hs, Adjudicator.statusOf_setStatus,
                    if_neg (Ne.symm hac)]
                  exact hst
              | reclaim l v =>
                by_cases hlc : l = c
                · subst hlc
                  obtain ⟨oL, -, -, -, -, hfo, -, -, -, -, -, -, -, -⟩ := Adjudicator.reclaim_some h
                  rw [hfo1] at hfo; exact absurd hfo (by simp)
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
                  have hp' : p ∈ ss'.signers := hproof'.2.2 p (hproof'.1 ▸ hp)
                  have hmem : ss' ∈ (Op.conclude c' ss').proofStates := by simp [Op.proofStates]
                  obtain ⟨x, hxmem, hxeq⟩ := hU ss' hmem hp'
                  have hΩ' := hfinal x hxmem (hxeq ▸ hproof'.1) (hxeq ▸ hproof'.2.1)
                  simp [Adjudicator.finalizedWith_channel, hxeq ▸ hΩ']
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
    (hc : apps c.appDef = consensusRules) (hp : p ∈ c.participants)
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
  · have hinv2 := latest_wait_keeps_status hbounds hc hp hchs hT0 hseq2 hlatest hfinal (Or.inr hst)
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
    (A : Assumptions apps p T) (net : NetworkState E p)
    (_hr : (Nitro.participant apps T).Reachable net) (c : FixedPart) (ss : SignedState E)
    (hc : apps c.appDef = consensusRules) (hp : p ∈ c.participants)
    (hh : net.Holds ss) (hall : ss.ByAll) (hchan : ss.state.channel = c)
    (hlatest : ∀ t ∈ net.sent, t.state.channel = c →
      t.state.turnNum < ss.state.turnNum ∨ t.state = ss.state)
    (hfinal : ∀ t ∈ net.sent, t.state.channel = c → t.state.isFinal = true →
      t.state.outcome = ss.state.outcome)
    (hdur : 2 * T.ε ≤ c.challengeDuration)
    (hst : net.Finalized c ss.state.outcome ∨
      (∃ t, net.chain.statusOf c = .open t ∧ t ≤ ss.state.turnNum) ∨
      (∃ t ch, net.chain.statusOf c = .challenged t ch ∧
        (t < ss.state.turnNum ∨ ch.state = ss.state) ∧ net.chain.now + T.ε ≤ ch.deadline)) :
    Finalizable apps T c ss.state.outcome net := by
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
    have hinv2 := latest_wait_keeps_status A.toBounds hc hp hch2s hT0 hseq2 hlatest2 hfinal2
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
    (by simpa [HonestMove.Feasible_chain, Op.HonestFeasible, Op.proofStates] using hh) ?_
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
    simpa [NetworkState.Finalized, NetworkState.applyHonest_chain] using hfz'
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
    wait. -/
theorem latest_state_finalizable_two (apps : Apps E) {p : Participant} (T : Threat E p)
    (A : Assumptions apps p T) (net : NetworkState E p)
    (_hr : (Nitro.participant apps T).Reachable net)
    (c1 c2 : FixedPart) (ss1 ss2 : SignedState E) (hne : c1 ≠ c2)
    (hc1 : apps c1.appDef = consensusRules) (hc2 : apps c2.appDef = consensusRules)
    (hp1 : p ∈ c1.participants) (hp2 : p ∈ c2.participants)
    (hh1 : net.Holds ss1) (hh2 : net.Holds ss2)
    (hall1 : ss1.ByAll) (hall2 : ss2.ByAll)
    (hchan1 : ss1.state.channel = c1) (hchan2 : ss2.state.channel = c2)
    (hlatest1 : ∀ t ∈ net.sent, t.state.channel = c1 →
      t.state.turnNum < ss1.state.turnNum ∨ t.state = ss1.state)
    (hlatest2 : ∀ t ∈ net.sent, t.state.channel = c2 →
      t.state.turnNum < ss2.state.turnNum ∨ t.state = ss2.state)
    (hfinal1 : ∀ t ∈ net.sent, t.state.channel = c1 → t.state.isFinal = true →
      t.state.outcome = ss1.state.outcome)
    (hfinal2 : ∀ t ∈ net.sent, t.state.channel = c2 → t.state.isFinal = true →
      t.state.outcome = ss2.state.outcome)
    (hdur1 : 2 * T.ε ≤ c1.challengeDuration) (hdur2 : 2 * T.ε ≤ c2.challengeDuration)
    (hst1 : (∃ t, net.chain.statusOf c1 = .open t ∧ t ≤ ss1.state.turnNum) ∨
      (∃ t ch, net.chain.statusOf c1 = .challenged t ch ∧
        (t < ss1.state.turnNum ∨ ch.state = ss1.state) ∧ net.chain.now + T.ε ≤ ch.deadline))
    (hst2 : (∃ t, net.chain.statusOf c2 = .open t ∧ t ≤ ss2.state.turnNum) ∨
      (∃ t ch, net.chain.statusOf c2 = .challenged t ch ∧
        (t < ss2.state.turnNum ∨ ch.state = ss2.state) ∧ net.chain.now + T.ε ≤ ch.deadline)) :
    Unbeatable apps T
      (fun n => n.Finalized c1 ss1.state.outcome ∧ n.Finalized c2 ss2.state.outcome) net := by
  have finish2 : ∀ (net2 : NetworkState E p),
      (net2.chain.finalizedWith c1.address = some ss1.state.outcome ∨
        ∃ T0 ch, net2.chain.statusOf c1 = .challenged T0 ch ∧ ss1.state.turnNum ≤ T0 ∧
          ch.state = ss1.state ∧ net2.chain.now ≤ ch.deadline) →
      (net2.chain.finalizedWith c2.address = some ss2.state.outcome ∨
        ∃ T0 ch, net2.chain.statusOf c2 = .challenged T0 ch ∧ ss2.state.turnNum ≤ T0 ∧
          ch.state = ss2.state ∧ net2.chain.now ≤ ch.deadline) →
      net2.sent = net.sent →
      UnbeatableIn apps T (fun _ => True)
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
    refine UnbeatableIn.move (.wait (max d1 d2 - net2.chain.now)) trivial trivial ?_
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
      exact wait_resolves_challenge A.toBounds hc1 hp1 hle1 hdw1 hlatest1' hfinal1' hseq2 hb1'
    · show (net3.applyHonest (.wait (max d1 d2 - net2.chain.now))).Finalized c2 ss2.state.outcome
      show (net3.chain.tick (max d1 d2 - net2.chain.now)).finalizedWith c2.address =
        some ss2.state.outcome
      exact wait_resolves_challenge A.toBounds hc2 hp2 hle2 hdw2 hlatest2' hfinal2' hseq2 hb2'
  have hfeasR : Reaction.Feasible net
      ⟨[Op.challenge c1 [ss1] ss1.state, Op.challenge c2 [ss2] ss2.state], []⟩ := by
    intro op hop
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hop
    rcases hop with rfl | rfl
    · simpa [Op.HonestFeasible, Op.proofStates] using hh1
    · simpa [Op.HonestFeasible, Op.proofStates] using hh2
  refine UnbeatableIn.move
    (.react ⟨[Op.challenge c1 [ss1] ss1.state, Op.challenge c2 [ss2] ss2.state], []⟩) trivial
    hfeasR ?_
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
  have hinv := latest_round_keeps_status_two A.toBounds hne hc1 hc2 hp1 hp2 hall1 hchan1 hall2
    hchan2 hdur1 hdur2 net.chain.now rfl hseq hεbound hlatest1 hlatest2 hfinal1 hfinal2 hbase1
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
    simp [NetworkState.applyHonest]
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
    (hc : apps c.appDef = consensusRules) (hp : p ∈ c.participants)
    (hdur : 2 * T.ε ≤ c.challengeDuration) :
    ∀ {net net' : NetworkState E p} {t : Time}, Threat.RoundSeq apps T t [] net net' →
      net'.chain.now < net.chain.now + T.ε →
      (∀ t0 ∈ net.sent, t0.state.channel = c →
        (t0.state.turnNum < ss.state.turnNum ∨ t0.state = ss.state) ∧ t0.state.isFinal = false) →
      ((∃ T0, net.chain.statusOf c = .open T0 ∧ ss.state.turnNum ≤ T0) ∨
        (∃ T0 ch, net.chain.statusOf c = .challenged T0 ch ∧ ss.state.turnNum ≤ T0 ∧
          net'.chain.now < ch.deadline)) →
      (∃ T0, net'.chain.statusOf c = .open T0 ∧ ss.state.turnNum ≤ T0) ∨
        (∃ T0 ch, net'.chain.statusOf c = .challenged T0 ch ∧ ss.state.turnNum ≤ T0 ∧
          net'.chain.now < ch.deadline) := by
  intro net net' t hseq
  generalize hpnil : ([] : List (Op E)) = pending at hseq
  induction hseq with
  | nil => intro _ _ hbase; exact hbase
  | land hsplit _ _ => rw [← hpnil] at hsplit; simp at hsplit
  | @tick pending net1 net2 dt hfeas hgate hrest ih =>
    intro hεbound hsent hbase
    have step : ((∃ T0, net1.chain.statusOf c = .open T0 ∧ ss.state.turnNum ≤ T0) ∨
        (∃ T0 ch, net1.chain.statusOf c = .challenged T0 ch ∧ ss.state.turnNum ≤ T0 ∧
          net2.chain.now < ch.deadline)) →
        ((∃ T0, (net1.applyAdv apps (AdvMove.tick dt)).chain.statusOf c = .open T0 ∧
          ss.state.turnNum ≤ T0) ∨
        (∃ T0 ch, (net1.applyAdv apps (AdvMove.tick dt)).chain.statusOf c = .challenged T0 ch ∧
          ss.state.turnNum ≤ T0 ∧ net2.chain.now < ch.deadline)) := by
      intro hbase1
      rcases hbase1 with ⟨T0, ho, hT0⟩ | ⟨T0, ch, hst, hT0, hdd⟩
      · exact Or.inl ⟨T0, by simpa [NetworkState.applyAdv] using ho, hT0⟩
      · exact Or.inr ⟨T0, ch, by simpa [NetworkState.applyAdv] using hst, hT0, hdd⟩
    have hbase' := step hbase
    have hεbound' : net2.chain.now < (net1.applyAdv apps (AdvMove.tick dt)).chain.now + T.ε :=
      lt_of_lt_of_le hεbound
        (Nat.add_le_add_right (NetworkState.applyAdv_now_le apps net1 (.tick dt)) T.ε)
    have hsent' : ∀ t0 ∈ (net1.applyAdv apps (AdvMove.tick dt)).sent, t0.state.channel = c →
        (t0.state.turnNum < ss.state.turnNum ∨ t0.state = ss.state) ∧ t0.state.isFinal = false := by
      rw [NetworkState.applyAdv_sent]; exact hsent
    exact ih hpnil hεbound' hsent' hbase'
  | @other pending net1 net2 m hfeas hnotick hnoland hrest ih =>
    intro hεbound hsent hbase
    have hsupp : ∀ (proof : SupportProof E) (cand : State E),
        (∀ ss' ∈ proof, p ∈ ss'.signers → ∃ x ∈ net1.sent, x.state = ss'.state) →
        (apps c.appDef).supports c proof cand = true →
        cand.turnNum < ss.state.turnNum ∨ cand = ss.state := by
      intro proof cand hU hs
      rw [hc] at hs
      match proof, hs with
      | [ss'], hs =>
        simp only [consensusRules, Bool.and_eq_true, decide_eq_true_eq] at hs
        obtain ⟨⟨hss', hch⟩, hall'⟩ := hs
        obtain ⟨x, hx, hxs⟩ := hU ss' (List.mem_singleton_self _) (hall' p (hch ▸ hp))
        have hb := (hsent x hx (by rw [hxs]; exact hch)).1
        rw [hxs, hss'] at hb
        exact hb
    have hcb : ∀ (proof : SupportProof E) (cand : State E),
        (∀ ss' ∈ proof, p ∈ ss'.signers → ∃ x ∈ net1.sent, x.state = ss'.state) →
        (apps c.appDef).supports c proof cand = true →
        cand.turnNum ≤ ss.state.turnNum := by
      intro proof cand hU hs
      rcases hsupp proof cand hU hs with h1 | h2
      · exact le_of_lt h1
      · exact le_of_eq (by rw [h2])
    have step : ((∃ T0, net1.chain.statusOf c = .open T0 ∧ ss.state.turnNum ≤ T0) ∨
        (∃ T0 ch, net1.chain.statusOf c = .challenged T0 ch ∧ ss.state.turnNum ≤ T0 ∧
          net2.chain.now < ch.deadline)) →
        ((∃ T0, (net1.applyAdv apps m).chain.statusOf c = .open T0 ∧ ss.state.turnNum ≤ T0) ∨
        (∃ T0 ch, (net1.applyAdv apps m).chain.statusOf c = .challenged T0 ch ∧
          ss.state.turnNum ≤ T0 ∧ net2.chain.now < ch.deadline)) := by
      intro hbase1
      cases m with
      | tick dt => exact absurd rfl (hnotick dt)
      | land op => exact absurd rfl (hnoland op)
      | deliver _ => exact hbase1
      | chain caller op =>
        rcases hbase1 with ⟨T0, ho, hT0⟩ | ⟨T0, ch, hst, hT0, hdd⟩
        · simp only [NetworkState.applyAdv]
          cases h : net1.chain.apply apps caller op with
          | none => exact Or.inl ⟨T0, ho, hT0⟩
          | some s' =>
            have hfo1 : net1.chain.finalOutcome c.address = none := by
              simp only [FixedPart.address_eq, Adjudicator.finalOutcome_channel, ho,
                ChannelStatus.finalOutcome_open]
            have hU : ∀ ss' ∈ op.proofStates, p ∈ ss'.signers →
                ∃ x ∈ net1.sent, x.state = ss'.state :=
              fun ss' hmem hsig => (hbounds.unforgeable net1 caller op hfeas ss' hmem).1 hsig
            cases op with
            | deposit a e x =>
              obtain ⟨-, -, -, -, hs, -⟩ := Adjudicator.deposit_some h
              exact Or.inl ⟨T0, by rw [Adjudicator.statusOf_of_status hs]; exact ho, hT0⟩
            | tick dt =>
              have hs' : net1.chain.tick dt = s' := by simpa using h
              subst hs'
              exact Or.inl ⟨T0, by rw [Adjudicator.tick_statusOf]; exact ho, hT0⟩
            | transfer a b =>
              by_cases hac : a = c
              · subst hac
                obtain ⟨o, -, -, hfo, -, -, -, -, -, -, -, -⟩ := Adjudicator.transfer_some h
                rw [hfo1] at hfo; exact absurd hfo (by simp)
              · obtain ⟨_, _, _, _, _, _, _, _, hs, _, _, _⟩ := Adjudicator.transfer_some h
                exact Or.inl ⟨T0, by
                  rw [Adjudicator.statusOf_of_status hs, Adjudicator.statusOf_setStatus,
                    if_neg (Ne.symm hac)]; exact ho, hT0⟩
            | reclaim l v =>
              by_cases hlc : l = c
              · subst hlc
                obtain ⟨oL, -, -, -, -, hfo, -, -, -, -, -, -, -, -⟩ := Adjudicator.reclaim_some h
                rw [hfo1] at hfo; exact absurd hfo (by simp)
              · obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hsr, _, _⟩ := Adjudicator.reclaim_some h
                exact Or.inl ⟨T0, by
                  rw [hsr, Adjudicator.statusOf_setStatus, if_neg (Ne.symm hlc)]; exact ho, hT0⟩
            | challenge c' proof cand =>
              by_cases hcc : c' = c
              · subst hcc
                obtain ⟨⟨-, hs, -, hmode⟩, rfl⟩ := Adjudicator.challenge_some h
                have hcbd : cand.turnNum ≤ ss.state.turnNum := hcb proof cand hU hs
                rcases hmode with ⟨-, hle2⟩ | ⟨hmo, -⟩
                · rw [ho, ChannelStatus.turnNumRecord_open] at hle2
                  refine Or.inr ⟨cand.turnNum,
                    Challenge.mk cand (net1.chain.now + c'.challengeDuration),
                    by rw [Adjudicator.statusOf_setStatus, if_pos rfl], by omega, ?_⟩
                  have hself : T.ε ≤ 2 * T.ε := by rw [Nat.two_mul]; exact Nat.le_add_left T.ε T.ε
                  have hge : T.ε ≤ c'.challengeDuration := le_trans hself hdur
                  exact lt_of_lt_of_le hεbound (Nat.add_le_add_left hge net1.chain.now)
                · exfalso
                  rw [Adjudicator.mode_eq, ho] at hmo
                  simp [ChannelStatus.mode_open] at hmo
              · obtain ⟨-, rfl⟩ := Adjudicator.challenge_some h
                exact Or.inl ⟨T0, by
                  rw [Adjudicator.statusOf_setStatus, if_neg (Ne.symm hcc)]; exact ho, hT0⟩
            | checkpoint c' proof cand =>
              by_cases hcc : c' = c
              · exfalso; subst hcc
                obtain ⟨⟨-, hs, -, hlt2⟩, -⟩ := Adjudicator.checkpoint_some h
                have hcbd : cand.turnNum ≤ ss.state.turnNum := hcb proof cand hU hs
                rw [ho, ChannelStatus.turnNumRecord_open] at hlt2
                omega
              · obtain ⟨-, rfl⟩ := Adjudicator.checkpoint_some h
                exact Or.inl ⟨T0, by
                  rw [Adjudicator.statusOf_setStatus, if_neg (Ne.symm hcc)]; exact ho, hT0⟩
            | conclude c' ss' =>
              by_cases hcc : c' = c
              · exfalso; subst hcc
                obtain ⟨⟨-, hproof'⟩, -⟩ := Adjudicator.conclude_some h
                have hp' : p ∈ ss'.signers := hproof'.2.2 p (hproof'.1 ▸ hp)
                have hmem : ss' ∈ (Op.conclude c' ss').proofStates := by simp [Op.proofStates]
                obtain ⟨x, hxmem, hxeq⟩ := hU ss' hmem hp'
                have hnf := (hsent x hxmem (by rw [hxeq]; exact hproof'.1)).2
                have hxfinal : x.state.isFinal = true := by rw [hxeq]; exact hproof'.2.1
                simp [hnf] at hxfinal
              · obtain ⟨-, rfl⟩ := Adjudicator.conclude_some h
                exact Or.inl ⟨T0, by
                  rw [Adjudicator.statusOf_setStatus, if_neg (Ne.symm hcc)]; exact ho, hT0⟩
        · have hmono : net1.chain.now ≤ net2.chain.now :=
            le_trans (NetworkState.applyAdv_now_le apps net1 (.chain caller op)) hrest.now_le
          have hltdl : net1.chain.now < ch.deadline := lt_of_le_of_lt hmono hdd
          have hm1 : net1.chain.mode c = .challenge := by
            rw [Adjudicator.mode_eq, hst, ChannelStatus.mode_challenged, if_neg (not_le.mpr hltdl)]
          simp only [NetworkState.applyAdv]
          cases h : net1.chain.apply apps caller op with
          | none => exact Or.inr ⟨T0, ch, hst, hT0, hdd⟩
          | some s' =>
            have hfo1 : net1.chain.finalOutcome c.address = none := by
              simp only [FixedPart.address_eq, Adjudicator.finalOutcome_channel, hst,
                ChannelStatus.finalOutcome_challenged, if_neg (not_le.mpr hltdl)]
            have hU : ∀ ss' ∈ op.proofStates, p ∈ ss'.signers →
                ∃ x ∈ net1.sent, x.state = ss'.state :=
              fun ss' hmem hsig => (hbounds.unforgeable net1 caller op hfeas ss' hmem).1 hsig
            cases op with
            | deposit a e x =>
              obtain ⟨-, -, -, -, hs, -⟩ := Adjudicator.deposit_some h
              exact Or.inr ⟨T0, ch, by rw [Adjudicator.statusOf_of_status hs]; exact hst, hT0, hdd⟩
            | tick dt =>
              have hs' : net1.chain.tick dt = s' := by simpa using h
              subst hs'
              exact Or.inr ⟨T0, ch, by rw [Adjudicator.tick_statusOf]; exact hst, hT0, hdd⟩
            | transfer a b =>
              by_cases hac : a = c
              · subst hac
                obtain ⟨o, -, -, hfo, -, -, -, -, -, -, -, -⟩ := Adjudicator.transfer_some h
                rw [hfo1] at hfo; exact absurd hfo (by simp)
              · obtain ⟨_, _, _, _, _, _, _, _, hs, _, _, _⟩ := Adjudicator.transfer_some h
                exact Or.inr ⟨T0, ch, by
                  rw [Adjudicator.statusOf_of_status hs, Adjudicator.statusOf_setStatus,
                    if_neg (Ne.symm hac)]; exact hst, hT0, hdd⟩
            | reclaim l v =>
              by_cases hlc : l = c
              · subst hlc
                obtain ⟨oL, -, -, -, -, hfo, -, -, -, -, -, -, -, -⟩ := Adjudicator.reclaim_some h
                rw [hfo1] at hfo; exact absurd hfo (by simp)
              · obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hsr, _, _⟩ := Adjudicator.reclaim_some h
                exact Or.inr ⟨T0, ch, by
                  rw [hsr, Adjudicator.statusOf_setStatus, if_neg (Ne.symm hlc)]; exact hst, hT0,
                  hdd⟩
            | challenge c' proof cand =>
              by_cases hcc : c' = c
              · exfalso; subst hcc
                obtain ⟨⟨-, hs, -, hmode⟩, -⟩ := Adjudicator.challenge_some h
                have hcbd : cand.turnNum ≤ ss.state.turnNum := hcb proof cand hU hs
                rcases hmode with ⟨hmo, -⟩ | ⟨-, hlt2⟩
                · rw [hm1] at hmo; exact absurd hmo (by decide)
                · rw [hst, ChannelStatus.turnNumRecord_challenged] at hlt2; omega
              · obtain ⟨-, rfl⟩ := Adjudicator.challenge_some h
                exact Or.inr ⟨T0, ch, by
                  rw [Adjudicator.statusOf_setStatus, if_neg (Ne.symm hcc)]; exact hst, hT0, hdd⟩
            | checkpoint c' proof cand =>
              by_cases hcc : c' = c
              · exfalso; subst hcc
                obtain ⟨⟨-, hs, -, hlt2⟩, -⟩ := Adjudicator.checkpoint_some h
                have hcbd : cand.turnNum ≤ ss.state.turnNum := hcb proof cand hU hs
                rw [hst, ChannelStatus.turnNumRecord_challenged] at hlt2; omega
              · obtain ⟨-, rfl⟩ := Adjudicator.checkpoint_some h
                exact Or.inr ⟨T0, ch, by
                  rw [Adjudicator.statusOf_setStatus, if_neg (Ne.symm hcc)]; exact hst, hT0, hdd⟩
            | conclude c' ss' =>
              by_cases hcc : c' = c
              · exfalso; subst hcc
                obtain ⟨⟨-, hproof'⟩, -⟩ := Adjudicator.conclude_some h
                have hp' : p ∈ ss'.signers := hproof'.2.2 p (hproof'.1 ▸ hp)
                have hmem : ss' ∈ (Op.conclude c' ss').proofStates := by simp [Op.proofStates]
                obtain ⟨x, hxmem, hxeq⟩ := hU ss' hmem hp'
                have hnf := (hsent x hxmem (by rw [hxeq]; exact hproof'.1)).2
                have hxfinal : x.state.isFinal = true := by rw [hxeq]; exact hproof'.2.1
                simp [hnf] at hxfinal
              · obtain ⟨-, rfl⟩ := Adjudicator.conclude_some h
                exact Or.inr ⟨T0, ch, by
                  rw [Adjudicator.statusOf_setStatus, if_neg (Ne.symm hcc)]; exact hst, hT0, hdd⟩
    have hbase' := step hbase
    have hεbound' : net2.chain.now < (net1.applyAdv apps m).chain.now + T.ε :=
      lt_of_lt_of_le hεbound (Nat.add_le_add_right (NetworkState.applyAdv_now_le apps net1 m) T.ε)
    have hsent' : ∀ t0 ∈ (net1.applyAdv apps m).sent, t0.state.channel = c →
        (t0.state.turnNum < ss.state.turnNum ∨ t0.state = ss.state) ∧ t0.state.isFinal = false := by
      rw [NetworkState.applyAdv_sent]; exact hsent
    exact ih hpnil hεbound' hsent' hbase'

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
    (hc : apps c.appDef = consensusRules) (hp : p ∈ c.participants) (hall : ss.ByAll)
    (hchan : ss.state.channel = c) (hdur : 2 * T.ε ≤ c.challengeDuration)
    {net net' : NetworkState E p} (t : Time) (ht : t = net.chain.now)
    (hseq : Threat.RoundSeq apps T t [Op.checkpoint c [ss] ss.state] net net') :
    net'.chain.now < net.chain.now + T.ε →
    (∀ t0 ∈ net.sent, t0.state.channel = c →
      (t0.state.turnNum < ss.state.turnNum ∨ t0.state = ss.state) ∧ t0.state.isFinal = false) →
    ((∃ t0, net.chain.statusOf c = .open t0 ∧ t0 ≤ ss.state.turnNum) ∨
      (∃ t0 ch, net.chain.statusOf c = .challenged t0 ch ∧
        (t0 < ss.state.turnNum ∨ ch.state = ss.state) ∧ net'.chain.now < ch.deadline)) →
    (∃ T0, net'.chain.statusOf c = .open T0 ∧ ss.state.turnNum ≤ T0) ∨
      (∃ T0 ch, net'.chain.statusOf c = .challenged T0 ch ∧ ss.state.turnNum ≤ T0 ∧
        net'.chain.now < ch.deadline) := by
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
            (∃ T0, (net1.applyAdv apps (AdvMove.land (Op.checkpoint c [ss] ss.state))).chain.statusOf
              c = .open T0 ∧ ss.state.turnNum ≤ T0) ∨
            (∃ T0 ch, (net1.applyAdv apps (AdvMove.land (Op.checkpoint c [ss] ss.state))).chain.statusOf
              c = .challenged T0 ch ∧ ss.state.turnNum ≤ T0 ∧ net2.chain.now < ch.deadline) := by
          rcases hbase with ⟨t0, ho, hle⟩ | ⟨t0, ch0, hst0, hdis0, hdd0⟩
          · by_cases hlt0 : t0 < ss.state.turnNum
            · have hcond : (net1.chain.statusOf c).IsOpen net1.chain.now ∧
                  (apps c.appDef).supports c [ss] ss.state = true ∧ ss.state.channel = c ∧
                  (net1.chain.statusOf c).turnNumRecord < ss.state.turnNum := by
                refine ⟨?_, by rw [hc]; simp [consensusRules, hchan, hall], hchan, ?_⟩
                · rw [ho]; simp [ChannelStatus.IsOpen, ChannelStatus.mode_open]
                · rw [ho, ChannelStatus.turnNumRecord_open]; exact hlt0
              have hop : net1.chain.apply apps p (Op.checkpoint c [ss] ss.state) =
                  some (net1.chain.setStatus c (.open ss.state.turnNum)) := by
                rw [Adjudicator.apply_checkpoint]; unfold Adjudicator.checkpoint
                rw [if_pos hcond]
              simp only [NetworkState.applyAdv, hop]
              exact Or.inl ⟨ss.state.turnNum,
                by rw [Adjudicator.statusOf_setStatus, if_pos rfl], le_refl _⟩
            · have hle2 : ss.state.turnNum ≤ t0 := not_lt.mp hlt0
              have hcondneg : ¬ ((net1.chain.statusOf c).IsOpen net1.chain.now ∧
                  (apps c.appDef).supports c [ss] ss.state = true ∧ ss.state.channel = c ∧
                  (net1.chain.statusOf c).turnNumRecord < ss.state.turnNum) := by
                rintro ⟨-, -, -, hlt2⟩
                rw [ho, ChannelStatus.turnNumRecord_open] at hlt2
                exact hlt0 hlt2
              have hop : net1.chain.apply apps p (Op.checkpoint c [ss] ss.state) = none := by
                rw [Adjudicator.apply_checkpoint]; unfold Adjudicator.checkpoint
                rw [if_neg hcondneg]
              simp only [NetworkState.applyAdv, hop]
              exact Or.inl ⟨t0, ho, hle2⟩
          · have hmono0 : net1.chain.now ≤ net2.chain.now :=
              le_trans
                (NetworkState.applyAdv_now_le apps net1 (.land (Op.checkpoint c [ss] ss.state)))
                hrest.now_le
            have hltdl0 : net1.chain.now < ch0.deadline := lt_of_le_of_lt hmono0 hdd0
            have hio0 : (net1.chain.statusOf c).IsOpen net1.chain.now := by
              rw [hst0, ChannelStatus.IsOpen, ChannelStatus.mode_challenged,
                if_neg (not_le.mpr hltdl0)]
              decide
            by_cases hlt0 : t0 < ss.state.turnNum
            · have hcond : (net1.chain.statusOf c).IsOpen net1.chain.now ∧
                  (apps c.appDef).supports c [ss] ss.state = true ∧ ss.state.channel = c ∧
                  (net1.chain.statusOf c).turnNumRecord < ss.state.turnNum := by
                refine ⟨hio0, by rw [hc]; simp [consensusRules, hchan, hall], hchan, ?_⟩
                rw [hst0, ChannelStatus.turnNumRecord_challenged]; exact hlt0
              have hop : net1.chain.apply apps p (Op.checkpoint c [ss] ss.state) =
                  some (net1.chain.setStatus c (.open ss.state.turnNum)) := by
                rw [Adjudicator.apply_checkpoint]; unfold Adjudicator.checkpoint
                rw [if_pos hcond]
              simp only [NetworkState.applyAdv, hop]
              exact Or.inl ⟨ss.state.turnNum,
                by rw [Adjudicator.statusOf_setStatus, if_pos rfl], le_refl _⟩
            · have hle2 : ss.state.turnNum ≤ t0 := not_lt.mp hlt0
              have hcondneg : ¬ ((net1.chain.statusOf c).IsOpen net1.chain.now ∧
                  (apps c.appDef).supports c [ss] ss.state = true ∧ ss.state.channel = c ∧
                  (net1.chain.statusOf c).turnNumRecord < ss.state.turnNum) := by
                rintro ⟨-, -, -, hlt2⟩
                rw [hst0, ChannelStatus.turnNumRecord_challenged] at hlt2
                exact hlt0 hlt2
              have hop : net1.chain.apply apps p (Op.checkpoint c [ss] ss.state) = none := by
                rw [Adjudicator.apply_checkpoint]; unfold Adjudicator.checkpoint
                rw [if_neg hcondneg]
              simp only [NetworkState.applyAdv, hop]
              exact Or.inr ⟨t0, ch0, hst0, hle2, hdd0⟩
        have hεbound' : net2.chain.now <
            (net1.applyAdv apps (AdvMove.land (Op.checkpoint c [ss] ss.state))).chain.now + T.ε :=
          lt_of_lt_of_le hεbound
            (Nat.add_le_add_right
              (NetworkState.applyAdv_now_le apps net1 (.land (Op.checkpoint c [ss] ss.state))) T.ε)
        have hsent_land : ∀ t0 ∈
            (net1.applyAdv apps (AdvMove.land (Op.checkpoint c [ss] ss.state))).sent,
            t0.state.channel = c →
            (t0.state.turnNum < ss.state.turnNum ∨ t0.state = ss.state) ∧
              t0.state.isFinal = false := by
          rw [NetworkState.applyAdv_sent]; exact hsent
        exact late_round_keeps_status_nil hbounds hc hp hdur hrest hεbound' hsent_land hbase_land
      · simp at hsplit
    · simp at hsplit
  | @tick pending net1 net2 dt hfeas hgate hrest ih =>
    intro hεbound hsent hbase
    have step : ((∃ t0, net1.chain.statusOf c = .open t0 ∧ t0 ≤ ss.state.turnNum) ∨
        (∃ t0 ch, net1.chain.statusOf c = .challenged t0 ch ∧
          (t0 < ss.state.turnNum ∨ ch.state = ss.state) ∧ net2.chain.now < ch.deadline)) →
        ((∃ t0, (net1.applyAdv apps (AdvMove.tick dt)).chain.statusOf c = .open t0 ∧
          t0 ≤ ss.state.turnNum) ∨
        (∃ t0 ch, (net1.applyAdv apps (AdvMove.tick dt)).chain.statusOf c = .challenged t0 ch ∧
          (t0 < ss.state.turnNum ∨ ch.state = ss.state) ∧ net2.chain.now < ch.deadline)) := by
      intro hbase1
      rcases hbase1 with ⟨t0, ho, hle⟩ | ⟨t0, ch, hst, hdis, hdd⟩
      · exact Or.inl ⟨t0, by simpa [NetworkState.applyAdv] using ho, hle⟩
      · exact Or.inr ⟨t0, ch, by simpa [NetworkState.applyAdv] using hst, hdis, hdd⟩
    have hbase' := step hbase
    have hεbound' : net2.chain.now < (net1.applyAdv apps (AdvMove.tick dt)).chain.now + T.ε :=
      lt_of_lt_of_le hεbound
        (Nat.add_le_add_right (NetworkState.applyAdv_now_le apps net1 (.tick dt)) T.ε)
    have hsent' : ∀ t0 ∈ (net1.applyAdv apps (AdvMove.tick dt)).sent, t0.state.channel = c →
        (t0.state.turnNum < ss.state.turnNum ∨ t0.state = ss.state) ∧ t0.state.isFinal = false := by
      rw [NetworkState.applyAdv_sent]; exact hsent
    exact ih heq hεbound' hsent' hbase'
  | @other pending net1 net2 m hfeas hnotick hnoland hrest ih =>
    intro hεbound hsent hbase
    have hsupp : ∀ (proof : SupportProof E) (cand : State E),
        (∀ ss' ∈ proof, p ∈ ss'.signers → ∃ x ∈ net1.sent, x.state = ss'.state) →
        (apps c.appDef).supports c proof cand = true →
        cand.turnNum < ss.state.turnNum ∨ cand = ss.state := by
      intro proof cand hU hs
      rw [hc] at hs
      match proof, hs with
      | [ss'], hs =>
        simp only [consensusRules, Bool.and_eq_true, decide_eq_true_eq] at hs
        obtain ⟨⟨hss', hch⟩, hall'⟩ := hs
        obtain ⟨x, hx, hxs⟩ := hU ss' (List.mem_singleton_self _) (hall' p (hch ▸ hp))
        have hb := (hsent x hx (by rw [hxs]; exact hch)).1
        rw [hxs, hss'] at hb
        exact hb
    have step : ((∃ t0, net1.chain.statusOf c = .open t0 ∧ t0 ≤ ss.state.turnNum) ∨
        (∃ t0 ch, net1.chain.statusOf c = .challenged t0 ch ∧
          (t0 < ss.state.turnNum ∨ ch.state = ss.state) ∧ net2.chain.now < ch.deadline)) →
        ((∃ t0, (net1.applyAdv apps m).chain.statusOf c = .open t0 ∧ t0 ≤ ss.state.turnNum) ∨
        (∃ t0 ch, (net1.applyAdv apps m).chain.statusOf c = .challenged t0 ch ∧
          (t0 < ss.state.turnNum ∨ ch.state = ss.state) ∧ net2.chain.now < ch.deadline)) := by
      intro hbase1
      cases m with
      | tick dt => exact absurd rfl (hnotick dt)
      | land op => exact absurd rfl (hnoland op)
      | deliver _ => exact hbase1
      | chain caller op =>
        rcases hbase1 with ⟨t0, ho, hle⟩ | ⟨t0, ch, hst, hdis, hdd⟩
        · simp only [NetworkState.applyAdv]
          cases h : net1.chain.apply apps caller op with
          | none => exact Or.inl ⟨t0, ho, hle⟩
          | some s' =>
            have hfo1 : net1.chain.finalOutcome c.address = none := by
              simp only [FixedPart.address_eq, Adjudicator.finalOutcome_channel, ho,
                ChannelStatus.finalOutcome_open]
            have hU : ∀ ss' ∈ op.proofStates, p ∈ ss'.signers →
                ∃ x ∈ net1.sent, x.state = ss'.state :=
              fun ss' hmem hsig => (hbounds.unforgeable net1 caller op hfeas ss' hmem).1 hsig
            cases op with
            | deposit a e x =>
              obtain ⟨-, -, -, -, hs, -⟩ := Adjudicator.deposit_some h
              refine Or.inl ⟨t0, ?_, hle⟩
              rw [Adjudicator.statusOf_of_status hs]; exact ho
            | tick dt =>
              have hs' : net1.chain.tick dt = s' := by simpa using h
              subst hs'
              refine Or.inl ⟨t0, ?_, hle⟩
              rw [Adjudicator.tick_statusOf]; exact ho
            | transfer a b =>
              by_cases hac : a = c
              · subst hac
                obtain ⟨o, -, -, hfo, -, -, -, -, -, -, -, -⟩ := Adjudicator.transfer_some h
                rw [hfo1] at hfo; exact absurd hfo (by simp)
              · obtain ⟨_, _, _, _, _, _, _, _, hs, _, _, _⟩ := Adjudicator.transfer_some h
                refine Or.inl ⟨t0, ?_, hle⟩
                rw [Adjudicator.statusOf_of_status hs, Adjudicator.statusOf_setStatus,
                  if_neg (Ne.symm hac)]
                exact ho
            | reclaim l v =>
              by_cases hlc : l = c
              · subst hlc
                obtain ⟨oL, -, -, -, -, hfo, -, -, -, -, -, -, -, -⟩ := Adjudicator.reclaim_some h
                rw [hfo1] at hfo; exact absurd hfo (by simp)
              · obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hsr, _, _⟩ := Adjudicator.reclaim_some h
                refine Or.inl ⟨t0, ?_, hle⟩
                rw [hsr, Adjudicator.statusOf_setStatus, if_neg (Ne.symm hlc)]
                exact ho
            | challenge c' proof cand =>
              by_cases hcc : c' = c
              · subst hcc
                obtain ⟨⟨-, hs, -, -⟩, rfl⟩ := Adjudicator.challenge_some h
                rcases hsupp proof cand hU hs with hlt | heqc
                · refine Or.inr ⟨cand.turnNum,
                    Challenge.mk cand (net1.chain.now + c'.challengeDuration), ?_, Or.inl hlt, ?_⟩
                  · rw [Adjudicator.statusOf_setStatus, if_pos rfl]
                  · have hself : T.ε ≤ 2 * T.ε := by rw [Nat.two_mul]; exact Nat.le_add_left T.ε T.ε
                    have hge : T.ε ≤ c'.challengeDuration := le_trans hself hdur
                    exact lt_of_lt_of_le hεbound (Nat.add_le_add_left hge net1.chain.now)
                · refine Or.inr ⟨cand.turnNum,
                    Challenge.mk cand (net1.chain.now + c'.challengeDuration), ?_, Or.inr heqc, ?_⟩
                  · rw [Adjudicator.statusOf_setStatus, if_pos rfl]
                  · have hself : T.ε ≤ 2 * T.ε := by rw [Nat.two_mul]; exact Nat.le_add_left T.ε T.ε
                    have hge : T.ε ≤ c'.challengeDuration := le_trans hself hdur
                    exact lt_of_lt_of_le hεbound (Nat.add_le_add_left hge net1.chain.now)
              · obtain ⟨-, rfl⟩ := Adjudicator.challenge_some h
                refine Or.inl ⟨t0, ?_, hle⟩
                rw [Adjudicator.statusOf_setStatus, if_neg (Ne.symm hcc)]
                exact ho
            | checkpoint c' proof cand =>
              by_cases hcc : c' = c
              · subst hcc
                obtain ⟨⟨-, hs, -, -⟩, rfl⟩ := Adjudicator.checkpoint_some h
                refine Or.inl ⟨cand.turnNum, ?_, ?_⟩
                · rw [Adjudicator.statusOf_setStatus, if_pos rfl]
                · rcases hsupp proof cand hU hs with hlt | heqc
                  · exact le_of_lt hlt
                  · exact le_of_eq (by rw [heqc])
              · obtain ⟨-, rfl⟩ := Adjudicator.checkpoint_some h
                refine Or.inl ⟨t0, ?_, hle⟩
                rw [Adjudicator.statusOf_setStatus, if_neg (Ne.symm hcc)]
                exact ho
            | conclude c' ss' =>
              by_cases hcc : c' = c
              · exfalso; subst hcc
                obtain ⟨⟨-, hproof'⟩, -⟩ := Adjudicator.conclude_some h
                have hp' : p ∈ ss'.signers := hproof'.2.2 p (hproof'.1 ▸ hp)
                have hmem : ss' ∈ (Op.conclude c' ss').proofStates := by simp [Op.proofStates]
                obtain ⟨x, hxmem, hxeq⟩ := hU ss' hmem hp'
                have hnf := (hsent x hxmem (by rw [hxeq]; exact hproof'.1)).2
                have hxfinal : x.state.isFinal = true := by rw [hxeq]; exact hproof'.2.1
                simp [hnf] at hxfinal
              · obtain ⟨-, rfl⟩ := Adjudicator.conclude_some h
                refine Or.inl ⟨t0, ?_, hle⟩
                rw [Adjudicator.statusOf_setStatus, if_neg (Ne.symm hcc)]
                exact ho
        · have hmono : net1.chain.now ≤ net2.chain.now :=
            le_trans (NetworkState.applyAdv_now_le apps net1 (.chain caller op)) hrest.now_le
          have hltdl : net1.chain.now < ch.deadline := lt_of_le_of_lt hmono hdd
          simp only [NetworkState.applyAdv]
          cases h : net1.chain.apply apps caller op with
          | none => exact Or.inr ⟨t0, ch, hst, hdis, hdd⟩
          | some s' =>
            have hfo1 : net1.chain.finalOutcome c.address = none := by
              simp only [FixedPart.address_eq, Adjudicator.finalOutcome_channel, hst,
                ChannelStatus.finalOutcome_challenged, if_neg (not_le.mpr hltdl)]
            have hU : ∀ ss' ∈ op.proofStates, p ∈ ss'.signers →
                ∃ x ∈ net1.sent, x.state = ss'.state :=
              fun ss' hmem hsig => (hbounds.unforgeable net1 caller op hfeas ss' hmem).1 hsig
            cases op with
            | deposit a e x =>
              obtain ⟨-, -, -, -, hs, -⟩ := Adjudicator.deposit_some h
              refine Or.inr ⟨t0, ch, ?_, hdis, hdd⟩
              rw [Adjudicator.statusOf_of_status hs]; exact hst
            | tick dt =>
              have hs' : net1.chain.tick dt = s' := by simpa using h
              subst hs'
              refine Or.inr ⟨t0, ch, ?_, hdis, hdd⟩
              rw [Adjudicator.tick_statusOf]; exact hst
            | transfer a b =>
              by_cases hac : a = c
              · subst hac
                obtain ⟨o, -, -, hfo, -, -, -, -, -, -, -, -⟩ := Adjudicator.transfer_some h
                rw [hfo1] at hfo; exact absurd hfo (by simp)
              · obtain ⟨_, _, _, _, _, _, _, _, hs, _, _, _⟩ := Adjudicator.transfer_some h
                refine Or.inr ⟨t0, ch, ?_, hdis, hdd⟩
                rw [Adjudicator.statusOf_of_status hs, Adjudicator.statusOf_setStatus,
                  if_neg (Ne.symm hac)]
                exact hst
            | reclaim l v =>
              by_cases hlc : l = c
              · subst hlc
                obtain ⟨oL, -, -, -, -, hfo, -, -, -, -, -, -, -, -⟩ := Adjudicator.reclaim_some h
                rw [hfo1] at hfo; exact absurd hfo (by simp)
              · obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hsr, _, _⟩ := Adjudicator.reclaim_some h
                refine Or.inr ⟨t0, ch, ?_, hdis, hdd⟩
                rw [hsr, Adjudicator.statusOf_setStatus, if_neg (Ne.symm hlc)]
                exact hst
            | challenge c' proof cand =>
              by_cases hcc : c' = c
              · subst hcc
                obtain ⟨⟨-, hs, -, -⟩, rfl⟩ := Adjudicator.challenge_some h
                rcases hsupp proof cand hU hs with hlt | heqc
                · refine Or.inr ⟨cand.turnNum,
                    Challenge.mk cand (net1.chain.now + c'.challengeDuration),
                    by rw [Adjudicator.statusOf_setStatus, if_pos rfl], Or.inl hlt, ?_⟩
                  have hself : T.ε ≤ 2 * T.ε := by rw [Nat.two_mul]; exact Nat.le_add_left T.ε T.ε
                  have hge : T.ε ≤ c'.challengeDuration := le_trans hself hdur
                  exact lt_of_lt_of_le hεbound (Nat.add_le_add_left hge net1.chain.now)
                · refine Or.inr ⟨cand.turnNum,
                    Challenge.mk cand (net1.chain.now + c'.challengeDuration),
                    by rw [Adjudicator.statusOf_setStatus, if_pos rfl], Or.inr heqc, ?_⟩
                  have hself : T.ε ≤ 2 * T.ε := by rw [Nat.two_mul]; exact Nat.le_add_left T.ε T.ε
                  have hge : T.ε ≤ c'.challengeDuration := le_trans hself hdur
                  exact lt_of_lt_of_le hεbound (Nat.add_le_add_left hge net1.chain.now)
              · obtain ⟨-, rfl⟩ := Adjudicator.challenge_some h
                refine Or.inr ⟨t0, ch, ?_, hdis, hdd⟩
                rw [Adjudicator.statusOf_setStatus, if_neg (Ne.symm hcc)]
                exact hst
            | checkpoint c' proof cand =>
              by_cases hcc : c' = c
              · subst hcc
                obtain ⟨⟨-, hs, -, -⟩, rfl⟩ := Adjudicator.checkpoint_some h
                refine Or.inl ⟨cand.turnNum,
                  by rw [Adjudicator.statusOf_setStatus, if_pos rfl], ?_⟩
                rcases hsupp proof cand hU hs with hlt | heqc
                · exact le_of_lt hlt
                · exact le_of_eq (by rw [heqc])
              · obtain ⟨-, rfl⟩ := Adjudicator.checkpoint_some h
                refine Or.inr ⟨t0, ch, ?_, hdis, hdd⟩
                rw [Adjudicator.statusOf_setStatus, if_neg (Ne.symm hcc)]
                exact hst
            | conclude c' ss' =>
              by_cases hcc : c' = c
              · exfalso; subst hcc
                obtain ⟨⟨-, hproof'⟩, -⟩ := Adjudicator.conclude_some h
                have hp' : p ∈ ss'.signers := hproof'.2.2 p (hproof'.1 ▸ hp)
                have hmem : ss' ∈ (Op.conclude c' ss').proofStates := by simp [Op.proofStates]
                obtain ⟨x, hxmem, hxeq⟩ := hU ss' hmem hp'
                have hnf := (hsent x hxmem (by rw [hxeq]; exact hproof'.1)).2
                have hxfinal : x.state.isFinal = true := by rw [hxeq]; exact hproof'.2.1
                simp [hnf] at hxfinal
              · obtain ⟨-, rfl⟩ := Adjudicator.conclude_some h
                refine Or.inr ⟨t0, ch, ?_, hdis, hdd⟩
                rw [Adjudicator.statusOf_setStatus, if_neg (Ne.symm hcc)]
                exact hst
    have hbase' := step hbase
    have hεbound' : net2.chain.now < (net1.applyAdv apps m).chain.now + T.ε :=
      lt_of_lt_of_le hεbound (Nat.add_le_add_right (NetworkState.applyAdv_now_le apps net1 m) T.ε)
    have hsent' : ∀ t0 ∈ (net1.applyAdv apps m).sent, t0.state.channel = c →
        (t0.state.turnNum < ss.state.turnNum ∨ t0.state = ss.state) ∧ t0.state.isFinal = false := by
      rw [NetworkState.applyAdv_sent]; exact hsent
    exact ih heq hεbound' hsent' hbase'

/-- ForceMove-B05. ForceMove:1511-1529: "as long as Alice notices Bob's challenge within
    the timeout period, she cannot hurt her position by playing on as though
    still in Collaborative mode ... all the moves made in Collaborative still
    stand." A participant who holds a supported state above the challenge
    state, and signed nothing above it, can bring the record to that turn
    before the deadline, with go-nitro `checkpoint`, and the channel is not
    finalized. The adversary can register that same state as a challenge, so
    the goal does not ask for Open mode. -/
theorem late_observer_can_checkpoint (apps : Apps E) {p : Participant} (T : Threat E p)
    (A : Assumptions apps p T) (net : NetworkState E p)
    (_hr : (Nitro.participant apps T).Reachable net) (c : FixedPart) (ss : SignedState E)
    (t : Nat) (ch : Challenge E) (hc : apps c.appDef = consensusRules) (hp : p ∈ c.participants)
    (hh : net.Holds ss) (hall : ss.ByAll) (hchan : ss.state.channel = c)
    (hsent : ∀ u ∈ net.sent, u.state.channel = c →
      (u.state.turnNum < ss.state.turnNum ∨ u.state = ss.state) ∧ u.state.isFinal = false)
    (hst : net.chain.statusOf c = .challenged t ch) (hgt : t < ss.state.turnNum)
    (hnow : net.chain.now + T.ε ≤ ch.deadline) (hdur : 2 * T.ε ≤ c.challengeDuration) :
    UnbeatableNoWait apps T
      (fun net' => net'.chain.mode c ≠ .finalized ∧
        ss.state.turnNum ≤ (net'.chain.statusOf c).turnNumRecord) net := by
  refine UnbeatableIn.move (.chain (.checkpoint c [ss] ss.state)) trivial
    (by simpa [HonestMove.Feasible_chain, Op.HonestFeasible, Op.proofStates] using hh) ?_
  intro net1 hround
  obtain ⟨hseq, hεbound⟩ := hround
  simp only [HonestMove.calls_chain] at hseq
  have hbase : (∃ t, net.chain.statusOf c = .open t ∧ t ≤ ss.state.turnNum) ∨
      (∃ t ch, net.chain.statusOf c = .challenged t ch ∧
        (t < ss.state.turnNum ∨ ch.state = ss.state) ∧ net1.chain.now < ch.deadline) :=
    Or.inr ⟨t, ch, hst, Or.inl hgt, lt_of_lt_of_le hεbound hnow⟩
  have hinv := late_round_keeps_status A.toBounds hc hp hall hchan hdur net.chain.now rfl hseq
    hεbound hsent hbase
  rcases hinv with ⟨t1, hopen1, hle1⟩ | ⟨t1, ch1, hchal1, hle1, hdd1⟩
  · apply UnbeatableIn.done
    show net1.chain.mode c ≠ .finalized ∧ ss.state.turnNum ≤ (net1.chain.statusOf c).turnNumRecord
    exact ⟨by rw [Adjudicator.mode_eq, hopen1]; simp,
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
      | react r => exact fun op hop => Op.HonestFeasible.not_tick (hfeas op hop)
      | wait _ => intro op hop; simp [HonestMove.calls] at hop
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
        simp [FixedPart.address_eq, hst, not_lt.mp hlt]
      exact Or.inr ⟨ch.state.outcome, hf, hf⟩
  | finalized r f o =>
    have hf : s.finalizedWith c.address = some f := by simp [FixedPart.address_eq, hst]
    exact Or.inr ⟨f, hf, hf⟩

omit [DecidableEq E] in
theorem ChanAgree.finalOutcome_left {c : FixedPart} {s1 s2 : Adjudicator E}
    (h : ChanAgree c s1 s2) : (s1.statusOf c).finalOutcome s1.now = none := by
  rcases h with ⟨r, h1, -⟩ | ⟨r, ch1, ch2, h1, -, -, hl1, -⟩
  · rw [h1]; rfl
  · rw [h1]; simp [not_le.mpr hl1]

omit [DecidableEq E] in
theorem ChanAgree.finalizedWith_left {c : FixedPart} {s1 s2 : Adjudicator E}
    (h : ChanAgree c s1 s2) : s1.finalizedWith c.address = none := by
  rcases h with ⟨r, h1, -⟩ | ⟨r, ch1, ch2, h1, -, -, hl1, -⟩
  · simp [FixedPart.address_eq, h1]
  · simp [FixedPart.address_eq, h1, not_le.mpr hl1]

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
      simp [FixedPart.address_eq, hnf] at hfa
    | reclaim l v =>
      obtain ⟨_, _, _, _, _, hfl, -, -, -, -, -, rfl, -, -⟩ := Adjudicator.reclaim_some h
      rw [Adjudicator.statusOf_setStatus, if_neg]
      rintro rfl
      simp [FixedPart.address_eq, hnf] at hfl
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
      simp at h; subst h; rfl

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
    · simp [Adjudicator.mode_eq, h1, h2]
    · simp [Adjudicator.mode_eq, h1, h2, not_le.mpr hl1, not_le.mpr hl2]
  have hrec : (s1.statusOf c).turnNumRecord = (s2.statusOf c).turnNumRecord := by
    rcases h with ⟨r, h1, h2⟩ | ⟨r, ch1, ch2, h1, h2, -, -, -⟩ <;> simp [h1, h2]
  have hopen1 : (s1.statusOf c).IsOpen s1.now := by
    rw [ChannelStatus.isOpen_iff_ne, ne_eq, ChannelStatus.mode_eq_finalized_iff, hnf1]; simp
  have hopen2 : (s2.statusOf c).IsOpen s2.now := by
    rw [ChannelStatus.isOpen_iff_ne, ne_eq, ChannelStatus.mode_eq_finalized_iff, hnf2]; simp
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
          · simp
          · simp
          · simp; omega
          · simp; omega
        · have hD0 : c'.challengeDuration = 0 := Nat.eq_zero_of_not_pos hD
          refine Or.inr ⟨cand.outcome, ?_, ?_⟩ <;> simp [FixedPart.address_eq, hD0]
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
        exact Or.inl (Or.inl ⟨cand.turnNum, by simp, by simp⟩)
      · exact Or.inl h
    · exact hneutral (by intro _ _ he; cases he) (fun _ _ he => hcc (Op.checkpoint.inj he).1)
        (by intro _ he; cases he)
  | conclude c' ss =>
    by_cases hcc : c' = c
    · subst hcc
      simp only [Adjudicator.apply_conclude, Adjudicator.conclude, hopen1, hopen2, true_and]
      split_ifs with hP
      · simp only [Option.getD_some]
        exact Or.inr ⟨ss.state.outcome, by simp [FixedPart.address_eq],
          by simp [FixedPart.address_eq]⟩
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

/-- Every signature of `p` or of `q` that either view received is on a
    state its signer sent, in that signer's own view. -/
def JointGenuine {p q : Participant} (Sp : NetworkState E p) (Sq : NetworkState E q) : Prop :=
  (∀ r ∈ Sp.received, SigOK p q Sp.sent Sq.sent r) ∧
  (∀ r ∈ Sq.received, SigOK p q Sp.sent Sq.sent r)

omit [DecidableEq E] in
theorem JointGenuine.symm {p q : Participant} {Sp : NetworkState E p} {Sq : NetworkState E q}
    (h : JointGenuine Sp Sq) : JointGenuine Sq Sp :=
  ⟨fun r hr => (h.2 r hr).swap, fun r hr => (h.1 r hr).swap⟩

omit [DecidableEq E] in
theorem NetworkState.Unforged.of_sent {p : Participant} {net net' : NetworkState E p}
    {ss : SignedState E} (hs : net.sent = net'.sent) (h : net.Unforged ss) : net'.Unforged ss := by
  unfold NetworkState.Unforged at *
  rw [← hs]
  exact h

omit [DecidableEq E] in
/-- A state `x` holds carries genuine signatures of `x` and of `y`, so the
    adversary of `y` may submit it (`NetworkState.Unforged`). -/
theorem NetworkState.Holds.sigOK {x y : Participant} (hxy : x ≠ y) {nx Sx : NetworkState E x}
    {Sy : NetworkState E y} (hrecv : ∀ r ∈ nx.received, r ∈ Sx.received)
    (hsent : nx.sent = Sx.sent) (hG : ∀ r ∈ Sx.received, SigOK x y Sx.sent Sy.sent r)
    {ss : SignedState E} (hh : nx.Holds ss) : SigOK x y Sx.sent Sy.sent ss ∧ Sy.Unforged ss := by
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
  refine ⟨⟨hx, hy⟩, hy, fun v hv hyv => ?_⟩
  rcases h2 v hv y hyv with ⟨hyx, -⟩ | ⟨r, hr, hrv, hry⟩
  · exact absurd hyx.symm hxy
  · obtain ⟨s, hs, hse⟩ := (hG r (hrecv r hr)).2 hry
    exact ⟨s, hs, by rw [hse]; exact hrv⟩

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
        ∀ ss ∈ op.proofStates, SigOK x y sx sy ss ∧ Sy.Unforged ss) →
      ChanAgreeOrFin c Sx.chain Sy.chain →
      (∀ r ∈ Sx.received, SigOK x y sx sy r) → (∀ r ∈ Sy.received, SigOK x y sx sy r) →
      ∃ Sx' Sy', Tx.RoundSeq apps t calls Sx Sx' ∧ OtherSteps apps Ty Sy Sy' ∧
        ChanAgreeOrFin c Sx'.chain Sy'.chain ∧
        (∀ r ∈ Sx'.received, SigOK x y sx sy r) ∧ (∀ r ∈ Sy'.received, SigOK x y sx sy r) ∧
        Sx'.chain.now = Sx.chain.now ∧ Sy'.chain.now = Sy.chain.now ∧ Sx'.sent = sx ∧
        Sy'.sent = sy := by
  intro calls
  induction calls with
  | nil =>
    intro Sx Sy hsx hsy _ hag hgx hgy
    exact ⟨Sx, Sy, .nil, .refl, hag, hgx, hgy, rfl, rfl, hsx, hsy⟩
  | cons op rest ih =>
    intro Sx Sy hsx hsy hcalls hag hgx hgy
    obtain ⟨hnt, hss⟩ := hcalls op List.mem_cons_self
    have hfeas : Ty.feasible Sy (.chain x op) :=
      Cy.capable Sy x op hxy (fun ss h => (hss ss h).2)
    have hag1 : ChanAgreeOrFin c (Sx.applyAdv apps (.land op)).chain
        (Sy.applyAdv apps (.chain x op)).chain := by
      rw [NetworkState.applyAdv_land_chain, NetworkState.applyAdv_chain_chain]
      exact hag.apply x hnt
    have hrest : ∀ op' ∈ rest, (∀ dt, op' ≠ .tick dt) ∧
        ∀ ss ∈ op'.proofStates, SigOK x y sx sy ss ∧
          (Sy.applyAdv apps (.chain x op)).Unforged ss := by
      intro op' hop'
      obtain ⟨hnt', hss'⟩ := hcalls op' (List.mem_cons_of_mem _ hop')
      exact ⟨hnt', fun ss h => ⟨(hss' ss h).1,
        (hss' ss h).2.of_sent (NetworkState.applyAdv_sent apps Sy _).symm⟩⟩
    obtain ⟨Sx', Sy', hseq, hSy, hag', hgx', hgy', hnx, hny, hsx', hsy'⟩ :=
      ih (Sx.applyAdv apps (.land op)) (Sy.applyAdv apps (.chain x op))
        (by rw [NetworkState.applyAdv_sent, hsx]) (by rw [NetworkState.applyAdv_sent, hsy])
        hrest hag1
        (fun r hr => (NetworkState.applyAdv_land_received apps Sx op r hr).elim
          (fun h => (hss r h).1) (hgx r))
        (fun r hr => (NetworkState.applyAdv_chain_received apps Sy x op r hr).elim
          (fun h => (hss r h).1) (hgy r))
    refine ⟨Sx', Sy', .land (l1 := []) (l2 := rest) rfl hseq,
      (OtherSteps.refl.tail hfeas (fun _ h => by cases h) (fun _ h => by cases h)).trans hSy,
      hag', hgx', hgy', ?_, ?_, hsx', hsy'⟩
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
            ∀ ss ∈ op.proofStates, SigOK p q Sp.sent Sq.sent ss ∧ Sq.Unforged ss := by
          intro op hop
          have hf : op.HonestFeasible np := hfeasp op hop
          exact ⟨hf.not_tick, fun ss hss =>
            (hf.holds ss hss).sigOK hpq hSp.received_subset hSp.sent_eq.symm hgen.1⟩
        obtain ⟨Sp', Sq', hseq, hSq', hag', hgp', hgq', hnp', hnq', hsp', hsq'⟩ :=
          mirror_land hpq Cq c np.chain.now Sp.sent Sq.sent rp.calls Sp Sq rfl rfl hcalls
            (Or.inl hA) hgen.1 hgen.2
        have hround : Tp.Round apps (.react rp) np Sp' :=
          ⟨hSp.roundSeq hseq, by rw [hnp', hnp]; exact Nat.lt_add_of_pos_right Tp.ε_pos⟩
        have hsub : ∀ s ∈ Sp.sent, s ∈ (Sp'.applyHonest (.react rp)).sent := by
          intro s hs
          show s ∈ rp.sends.map _ ++ Sp'.sent
          rw [hsp']
          exact List.mem_append_right _ hs
        refine ihp Sp' hround (Sp'.applyHonest (.react rp)) .refl rfl hUq Sq' (hSq.trans hSq')
          (by rw [hnq', hnq]) hag' ⟨fun r hr => ?_, fun r hr => ?_⟩
        · exact (hgp' r hr).mono hsub (fun s hs => by rw [hsq']; exact hs)
        · exact (hgq' r hr).mono hsub (fun s hs => by rw [hsq']; exact hs)
      | wait dp =>
        cases mq with
        | react rq =>
          -- `q` issues its reaction; its calls run in `p`'s open round.
          have hcalls : ∀ op ∈ rq.calls, (∀ dt, op ≠ .tick dt) ∧
              ∀ ss ∈ op.proofStates, SigOK q p Sq.sent Sp.sent ss ∧ Sp.Unforged ss := by
            intro op hop
            have hf : op.HonestFeasible nq := hfeasq op hop
            exact ⟨hf.not_tick, fun ss hss =>
              (hf.holds ss hss).sigOK (Ne.symm hpq) hSq.received_subset hSq.sent_eq.symm
                hgen.symm.1⟩
          obtain ⟨Sq', Sp', hseq, hSp', hag', hgq', hgp', hnq', hnp', hsq', hsp'⟩ :=
            mirror_land (Ne.symm hpq) Cp c nq.chain.now Sq.sent Sp.sent rq.calls Sq Sp rfl rfl
              hcalls (Or.inl hA.symm) hgen.symm.1 hgen.symm.2
          have hround : Tq.Round apps (.react rq) nq Sq' :=
            ⟨hSq.roundSeq hseq, by rw [hnq', hnq]; exact Nat.lt_add_of_pos_right Tq.ε_pos⟩
          have hsub : ∀ s ∈ Sq.sent, s ∈ (Sq'.applyHonest (.react rq)).sent := by
            intro s hs
            show s ∈ rq.sends.map _ ++ Sq'.sent
            rw [hsq']
            exact List.mem_append_right _ hs
          refine ihq Sq' hround Sp' (hSp.trans hSp') (by rw [hnp', hnp])
            (Sq'.applyHonest (.react rq)) .refl rfl hag'.symm ⟨fun r hr => ?_, fun r hr => ?_⟩
          · exact ((hgp' r hr).mono hsub (fun s hs => by rw [hsp']; exact hs)).swap
          · exact ((hgq' r hr).mono hsub (fun s hs => by rw [hsp']; exact hs)).swap
        | wait dq =>
          have hroundp : Tp.Round apps (.wait dp) np Sp :=
            ⟨hSp.roundSeq .nil, by rw [hnp]; exact Nat.lt_add_of_pos_right Tp.ε_pos⟩
          have hroundq : Tq.Round apps (.wait dq) nq Sq :=
            ⟨hSq.roundSeq .nil, by rw [hnq]; exact Nat.lt_add_of_pos_right Tq.ε_pos⟩
          rcases hA with ⟨r, ho1, ho2⟩ | ⟨r, ch1, ch2, hc1, hc2, hst, hlt1, hlt2⟩
          · -- `c` is open: `p`'s wait cannot finalize it.
            exact ihp Sp hroundp (Sp.applyHonest (.wait dp)) .refl rfl hUq Sq hSq hnq
              (Or.inl (Or.inl ⟨r, by simpa [NetworkState.applyHonest] using ho1, ho2⟩)) hgen
          · by_cases hout : ch1.state.outcome = Ω
            · -- The running challenge pays `p`'s outcome: `q` waits first.
              by_cases hcross : Sq.chain.now + dq < ch2.deadline
              · exact ihq Sq hroundq Sp hSp hnp (Sq.applyHonest (.wait dq)) .refl rfl
                  (Or.inl (Or.inr ⟨r, ch1, ch2, hc1,
                    by simpa [NetworkState.applyHonest] using hc2, hst, hlt1,
                    by simpa [NetworkState.applyHonest] using hcross⟩)) hgen
              · have hfin : (Sq.applyHonest (.wait dq)).chain.finalizedWith c.address = some Ω := by
                  simp only [NetworkState.applyHonest, Adjudicator.finalizedWith_channel,
                    FixedPart.address_eq, Adjudicator.tick_statusOf, Adjudicator.tick_now, hc2,
                    ChannelStatus.finalizedWith_challenged, if_pos (not_lt.mp hcross), ← hst, hout]
                exact (hcontq Sq hroundq).finalized_eq hfin
            · -- Any other running challenge: `p` waits first.
              by_cases hcross : Sp.chain.now + dp < ch1.deadline
              · exact ihp Sp hroundp (Sp.applyHonest (.wait dp)) .refl rfl hUq Sq hSq hnq
                  (Or.inl (Or.inr ⟨r, ch1, ch2, by simpa [NetworkState.applyHonest] using hc1,
                    hc2, hst, by simpa [NetworkState.applyHonest] using hcross, hlt2⟩)) hgen
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
    (n : Network E) (hr : (Nitro.network apps Ts).Reachable n) (hvn : v = n.views)
    (c : FixedPart) (p q : Participant) (hpq : p ≠ q) (Ω Ω' : Outcome E)
    (hp : Finalizable apps (Ts.T p) c Ω (v p)) (hq : Finalizable apps (Ts.T q) c Ω' (v q)) :
    Ω = Ω' := by
  subst hvn
  have hsig := Nitro.network_received_signers hr
  exact finalizable_joint hpq (Ts.ok p).toCapable (Ts.ok q).toCapable hp (n.views p) .refl rfl hq
    (n.views q) .refl rfl (ChanAgreeOrFin.refl c n.chain)
    ⟨fun r hr' => ⟨hsig p p r hr', hsig p q r hr'⟩, fun r hr' => ⟨hsig q p r hr', hsig q q r hr'⟩⟩

/-- Nitro-22. Nitro:597-611: "exactly one of the following statements is true
    about a channel χ at any point in time: 1. Finalized outcome ... 2. One
    participant has multiple finalizable outcomes ... 3. Multiple participants
    share one finalizable outcome ... 4. No finalizable outcomes." -/
theorem channel_finalizability_cases (apps : Apps E) (Ts : Threats E apps) (v : Views E)
    (n : Network E) (hr : (Nitro.network apps Ts).Reachable n)
    (hvn : v = n.views) (c : FixedPart) (p0 : Participant) :
    (∃ Ω, (v p0).Finalized c Ω) ∨
    (∃ p, p ∈ c.participants ∧ (∃ Ω, Finalizable apps (Ts.T p) c Ω (v p)) ∧
      ∀ q, q ∈ c.participants → q ≠ p → ∀ Ω, ¬ Finalizable apps (Ts.T q) c Ω (v q)) ∨
    (∃ Ω p q, p ∈ c.participants ∧ q ∈ c.participants ∧ p ≠ q ∧
      Finalizable apps (Ts.T p) c Ω (v p) ∧ Finalizable apps (Ts.T q) c Ω (v q) ∧
      ∀ r, r ∈ c.participants → ∀ Ω', Finalizable apps (Ts.T r) c Ω' (v r) → Ω' = Ω) ∨
    (∀ p, p ∈ c.participants → ∀ Ω, ¬ Finalizable apps (Ts.T p) c Ω (v p)) := by
  sorry

/-- Nitro-24. Nitro:653-656: "For any participant, p, in a channel, χ, exactly one
    of the following statements is true at a given point in time: 1. p has at
    least one finalizable outcome. 2. p has at least two enabled outcomes."
    The channel is past its setup: `p` holds a supported state of it. -/
theorem finalizable_or_two_enabled (apps : Apps E) {p : Participant} (T : Threat E p)
    (A : Assumptions apps p T) (net : NetworkState E p)
    (hr : (Nitro.participant apps T).Reachable net) (c : FixedPart) (hp : p ∈ c.participants)
    (hsupp : ∃ proof candidate, (∀ ss ∈ proof, net.Holds ss) ∧
      (apps c.appDef).supports c proof candidate = true ∧ candidate.channel = c)
    (hdur : 2 * T.ε ≤ c.challengeDuration) :
    (∃ Ω, Finalizable apps T c Ω net) ∨
    (∃ Ω1 Ω2, Ω1 ≠ Ω2 ∧ Enabled apps T c Ω1 net ∧ Enabled apps T c Ω2 net) := by
  sorry

/-- Nitro-24. Nitro:657-658: "if a participant has only enabled a single outcome,
    that outcome must be finalizable for them." `p` holds a support for every
    state of `c` it signed. -/
theorem single_enabled_is_finalizable (apps : Apps E) {p : Participant} (T : Threat E p)
    (A : Assumptions apps p T) (net : NetworkState E p)
    (hr : (Nitro.participant apps T).Reachable net) (c : FixedPart) (hp : p ∈ c.participants)
    (hsupp : ∀ t ∈ net.sent, t.state.channel = c → ∃ proof, (∀ ss ∈ proof, net.Holds ss) ∧
      (apps c.appDef).supports c proof t.state = true)
    (hdur : 2 * T.ε ≤ c.challengeDuration)
    (Ω : Outcome E) (hΩ : Enabled apps T c Ω net)
    (huniq : ∀ Ω', Enabled apps T c Ω' net → Ω' = Ω) :
    Finalizable apps T c Ω net := by
  sorry

/-- Nitro-23, ForceMove-B06, ForceMove-A06, ForceMove-A07. Nitro:635-636, Nitro:639-640: at the funding
    point, "After the first n states have been broadcast", the outcome is
    universally finalizable. ForceMove:862-871: the prefund states are "exactly what
    they need to launch a challenge on-chain to recover their funds". The
    setup phase keeps the outcome (ForceMove:1092-1125, ForceMove:1150-1184),
    and the game library accepts its transitions. -/
theorem funding_point_universally_finalizable (apps : Apps E) (Ts : Threats E apps) (v : Views E)
    (n : Network E) (hr : (Nitro.network apps Ts).Reachable n)
    (hvn : v = n.views) (c : FixedPart) (Ω : Outcome E) (vt : State E → State E → Bool)
    (hc : apps c.appDef = forceMoveRules vt) (hsetup : SetupPhaseKeepsOutcome vt c)
    (hvt : SetupPhaseAccepted vt c)
    (hn : 0 < c.n) (hdur : ∀ p, 2 * (Ts.T p).ε ≤ c.challengeDuration) (h : AtFundingPoint v c Ω)
    (hchain : ∀ p, (v p).chain.mode c = .open ∧ (v p).chain.statusOf c = .open 0) :
    UniversallyFinalizable apps Ts v c Ω := by
  sorry

/-- Nitro-23, ForceMove-A14. Nitro:637-640: "When a single conclusion proof is known to
    each participant ... the channel is in the concluded state." The
    concluded outcome is universally finalizable. -/
theorem concluded_universally_finalizable (apps : Apps E) (Ts : Threats E apps) (v : Views E)
    (n : Network E) (hr : (Nitro.network apps Ts).Reachable n)
    (hvn : v = n.views) (c : FixedPart) (Ω : Outcome E) (hc : apps c.appDef = consensusRules)
    (h : Concluded v c Ω)
    (hsent : ∀ p, ∀ t ∈ (v p).sent, t.state.channel = c → t.state.isFinal = true →
      t.state.outcome = Ω)
    (hchain : ∀ p, (v p).chain.finalizedWith c.address = none ∨ (v p).Finalized c Ω)
    (hdur : ∀ p, 2 * (Ts.T p).ε ≤ c.challengeDuration)
    (hpend : ∀ p, (v p).DeadlineAfter c (Ts.T p).ε) :
    UniversallyFinalizable apps Ts v c Ω := by
  subst hvn
  intro p hp
  obtain ⟨ss, hh, hproof, hΩ⟩ := h p hp
  exact UnbeatableIn.mono (fun _ _ => trivial)
    (conclusion_proof_finalizable apps (Ts.T p) (Ts.ok p) (n.views p)
      (Nitro.network_views_participant_reachable hr p) c ss Ω hc hp hh hproof hΩ
      (hsent p) (hchain p) (hdur p) (hpend p))

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
  · rcases h2 v hv q hq with ⟨hqp, s, hs, hse⟩ | ⟨r, hr, hre, hrq⟩
    · exact Or.inl ⟨hqp, s, hsent ▸ hs, hse⟩
    · exact Or.inr ⟨r, hrecv r hr, hre, hrq⟩

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
    simpa [FixedPart.address_eq] using hf
  have hfin : (s.statusOf c).mode s.now = .finalized := by
    rw [ChannelStatus.mode_eq_finalized_iff, hf0]; rfl
  cases op with
  | deposit a e x =>
    obtain ⟨⟨c', hac', -⟩, -, hb, -, hs, hn⟩ := Adjudicator.deposit_some h
    have had : a ≠ (Address.external d : Address E) := by rw [hac']; intro hh; cases hh
    refine ⟨o, amt, ?_, le_refl _, hd, ?_⟩
    · simpa [FixedPart.address_eq, Adjudicator.statusOf_of_status hs, hn] using hf
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
        simp [FixedPart.address_eq, hstatc]
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
          have heq : o.owed (Address.external d) = amt := by simp [Allocation.owed, hd]
          rw [heq] at hxb; exact hxb
        have htot' : (o.reduceOwed (Address.external d) x).total ≤ o.total := Nat.le.intro htot
        refine ⟨o.reduceOwed (Address.external d) x, amt - x, hfo', htot', hfind', ?_⟩
        rw [hbal, Balances.get_sub, if_neg hcd, Balances.get_add, if_pos rfl]
        grind
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
      · simpa [FixedPart.address_eq, hstatc, hnow] using hf
      · rw [hbal, Balances.get_sub, if_neg hcd, Balances.get_add]
        by_cases hbd : (Address.external d : Address E) = b
        · rw [if_pos hbd]; grind
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
        simp [FixedPart.address_eq, hstatl]
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
        · rw [if_pos hld, ← hld, Allocation.find_addTo_self, hd]; simp
        · rw [if_neg hld, Allocation.find_addTo_of_ne _ _ hld, hd]
      have hfind2 : ((o.addTo left (oV.amountAt 0)).addTo right (oV.amountAt 1)).find
          (Address.external d) = some ⟨Address.external d, .alloc
            ((if (Address.external d : Address E) = left then amt + oV.amountAt 0 else amt) +
              (if (Address.external d : Address E) = right then oV.amountAt 1 else 0))⟩ := by
        by_cases hrd : (Address.external d : Address E) = right
        · rw [if_pos hrd, ← hrd, Allocation.find_addTo_self, hfind1]; simp
        · rw [if_neg hrd, Allocation.find_addTo_of_ne _ _ hrd, hfind1]; simp
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
      split <;> split <;> grind
    · obtain ⟨oL, oV, x, left, right, hL, hV, hfind, -, -, hxeq, hsucc, hlk, hvk⟩ :=
        Adjudicator.reclaim_some h
      have hstatc : s'.statusOf c = s.statusOf c := by
        rw [hsucc, Adjudicator.statusOf_setStatus, if_neg (Ne.symm hcl)]
      have hnow : s'.now = s.now := by rw [hsucc]; rfl
      have hbal' : s'.balances = s.balances := by rw [hsucc]; rfl
      refine ⟨o, amt, ?_, le_refl _, hd, ?_⟩
      · simpa [FixedPart.address_eq, hstatc, hnow] using hf
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
      · simpa [FixedPart.address_eq, hstatc, hnow] using hf
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
      · simpa [FixedPart.address_eq, hstatc, hnow] using hf
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
      · simpa [FixedPart.address_eq, hstatc, hnow] using hf
      · rw [hbal']
  | tick dt =>
    have hs' : s.tick dt = s' := by simpa using h
    subst hs'
    refine ⟨o, amt, ?_, le_refl _, hd, ?_⟩
    · simpa [FixedPart.address_eq] using
        ChannelStatus.finalOutcome_mono hf0 (Nat.le_add_right s.now dt)
    · simp

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

omit [DecidableEq E] in
/-- A move's own feasibility, read call by call: `.wait` has none; a
    `.react r`'s feasibility is already exactly `∀op∈r.calls,
    op.HonestFeasible net`. Used by `funded_entry_unbeatable`'s `move`
    case, so `funded_entry_round` gets its feasibility hypothesis from
    `hfeas` without naming `net` or `m` explicitly (avoiding a `cases m`
    on a hypothesis that outlives the match). -/
theorem HonestMove.Feasible.calls {p : Participant} {net : NetworkState E p} {m : HonestMove E}
    (hfeas : m.Feasible net) : ∀ op ∈ m.calls, op.HonestFeasible net := by
  cases m with
  | react r => exact hfeas
  | wait dt => simp [HonestMove.calls]

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
    have hopfeas : op.HonestFeasible net1 := hpfeas op (by simp [hsplit])
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
      Machine.Reachable.tail hR (Or.inr (Or.inr (Or.inl ⟨.tick dt, hfeas, rfl⟩)))
    have hpfeas' : ∀ op' ∈ pending, op'.HonestFeasible (net1.applyAdv apps (.tick dt)) :=
      fun op' hop' => Op.HonestFeasible.applyAdv (.tick dt) (hpfeas op' hop')
    refine ih hpfeas' hR1 ?_ ?_
    · simpa [NetworkState.applyAdv, FixedPart.address_eq] using
        ChannelStatus.finalOutcome_mono
          (show (net1.chain.statusOf c).finalOutcome net1.chain.now = some (.allocation o) by
            simpa [FixedPart.address_eq] using hf)
          (Nat.le_add_right net1.chain.now dt)
    · simpa [NetworkState.applyAdv] using hd
  | @other pending net1 net2 m hfeas hnotick hnoland hrest ih =>
    intro hpfeas hR o amt hf hd
    have hR1 : (Nitro.participant apps T).Reachable (net1.applyAdv apps m) :=
      Machine.Reachable.tail hR (Or.inr (Or.inr (Or.inl ⟨m, hfeas, rfl⟩)))
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
        simpa [NetworkState.applyAdv, hm] using hres
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
      simpa [NetworkState.applyAdv] using hres
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
    · simp [NetworkState.applyHonest]


/-- One round of adversary play keeps an honest move feasible: `.wait` is
    always feasible; a `.react r`'s feasibility is "every call in `r.calls`
    is `Op.HonestFeasible`", each carried forward by `Op.HonestFeasible.round`.
    Used by `funded_entry_unbeatable`: the committed move's own feasibility
    (checked before the round) still holds at the state it is actually
    applied to (after the round). -/
theorem HonestMove.Feasible.round {apps : Apps E} {p : Participant} {T : Threat E p} {t : Time}
    {pending : List (Op E)} {net net' : NetworkState E p}
    (hseq : Threat.RoundSeq apps T t pending net net') {m : HonestMove E}
    (hfeas : m.Feasible net) : m.Feasible net' := by
  cases m with
  | react r => exact fun op hop => Op.HonestFeasible.round hseq (hfeas op hop)
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

    Operator ruling 2026-10-29: `net` is a reachable network state, for the
    same reason as `directly_funded_pays`. -/
theorem finalizable_funded_pays (apps : Apps E) {p : Participant} (T : Threat E p)
    (A : Assumptions apps p T) (net : NetworkState E p)
    (hr : (Nitro.participant apps T).Reachable net) (c : FixedPart) (o : Allocation E) (d : E)
    (hf : net.chain.finalOutcome c.address = some (.allocation o))
    (hfund : FundedFor apps T c o.total net) (amt : Coins)
    (hd : o.find (.external d) = some ⟨.external d, .alloc amt⟩) :
    CanObtain apps T (.external d) (net.chain.balances.get (.external d) + o.owed (.external d))
      net := by
  have howed : o.owed (Address.external d) = amt := by simp [Allocation.owed, hd]
  rw [howed]
  have hU : UnbeatableIn apps T (fun _ => True)
      (fun net' => net'.chain.DirectlyFundedWith c o.total) net := hfund
  have hU2 := funded_entry_unbeatable c o.total d hU hr hf hd
  refine UnbeatableIn.bind hU2 ?_
  rintro net' ⟨hR', o', amt', hf', htot', hfund', hd', hle'⟩
  have hDF : net'.chain.DirectlyFunded c := ⟨o', hf', le_trans htot' hfund'⟩
  have hpay := directly_funded_pays apps T A net' hR' c o' d hf' hDF amt' hd'
  have howed' : o'.owed (Address.external d) = amt' := by simp [Allocation.owed, hd']
  rw [howed'] at hpay
  have hpayMono : UnbeatableIn apps T (fun _ => True)
      (fun net'' => net'.chain.balances.get (.external d) + amt' ≤
        net''.chain.balances.get (.external d)) net' :=
    UnbeatableIn.mono (fun _ _ => trivial) hpay
  refine UnbeatableIn.imp ?_ hpayMono
  intro net'' hle''
  exact le_trans hle' hle''


/-- `ConsensusSafe` over a round's play with nothing of `p`'s own still
    pending: every operation that reaches channel `c` here is an adversary
    one, not `p`'s own checkpoint, so the invariant carries exactly as
    `hsupp`/`hconclude`/`hcheckpoint`/`hchallenge` bound it, with no land
    case to handle (`pending = []` rules it out structurally). Used by
    `consensus_round_safe` for the adversary play before `p`'s own
    checkpoint call lands, and after. -/
theorem consensus_round_safe_nil {apps : Apps E} {p : Participant} {T : Threat E p}
    (hbounds : Bounds apps p T) {c : FixedPart} {ss : SignedState E} {Ω1 Ω2 : Outcome E}
    (hc : apps c.appDef = consensusRules) (hp : p ∈ c.participants) (hΩ1 : ss.state.outcome = Ω1)
    (hdur : 2 * T.ε ≤ c.challengeDuration) :
    ∀ {net net' : NetworkState E p} {t : Time}, Threat.RoundSeq apps T t [] net net' →
      net'.chain.now < net.chain.now + T.ε →
      (∀ t0 ∈ net.sent, t0.state.channel = c →
        (t0.state.turnNum < ss.state.turnNum ∨ t0.state = ss.state ∨ t0.state.outcome = Ω2) ∧
        (t0.state.isFinal = true → t0.state.outcome = Ω1 ∨ t0.state.outcome = Ω2)) →
      ConsensusSafe c ss Ω1 Ω2 net net' → ConsensusSafe c ss Ω1 Ω2 net' net' := by
  intro net net' t hseq
  generalize hpnil : ([] : List (Op E)) = pending at hseq
  induction hseq with
  | nil => intro _ _ hbase; exact hbase
  | land hsplit _ _ => rw [← hpnil] at hsplit; simp at hsplit
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
              .open t := by simpa [NetworkState.applyAdv] using ho
          exact Or.inr (Or.inr ⟨by
            simp [FixedPart.address_eq, Adjudicator.finalizedWith_channel, hstatusc'],
            Or.inl ⟨t, hstatusc'⟩⟩)
        · have hnotexp : ¬ ch.deadline ≤ net1.chain.now := by
            intro hle
            have hcontra : net1.chain.finalizedWith c.address = some ch.state.outcome := by
              simp [FixedPart.address_eq, Adjudicator.finalizedWith_channel, hst,
                ChannelStatus.finalizedWith_challenged, hle]
            rw [hfn] at hcontra; exact absurd hcontra (by simp)
          rcases hdisj with h1 | h2 | ⟨hltC, hddC⟩
          · by_cases hexp2 : ch.deadline ≤ net1.chain.now + dt
            · exact Or.inl (by
                simp [NetworkState.applyAdv, FixedPart.address_eq,
                  Adjudicator.finalizedWith_channel, Adjudicator.tick_statusOf, hst,
                  ChannelStatus.finalizedWith_challenged, hexp2, h1])
            · refine Or.inr (Or.inr ⟨?_, Or.inr ⟨t, ch, ?_, Or.inl h1⟩⟩)
              · simp [NetworkState.applyAdv, FixedPart.address_eq,
                  Adjudicator.finalizedWith_channel, Adjudicator.tick_statusOf, hst,
                  ChannelStatus.finalizedWith_challenged, hexp2]
              · simpa [NetworkState.applyAdv, Adjudicator.tick_statusOf] using hst
          · by_cases hexp2 : ch.deadline ≤ net1.chain.now + dt
            · exact Or.inr (Or.inl (by
                simp [NetworkState.applyAdv, FixedPart.address_eq,
                  Adjudicator.finalizedWith_channel, Adjudicator.tick_statusOf, hst,
                  ChannelStatus.finalizedWith_challenged, hexp2, h2]))
            · refine Or.inr (Or.inr ⟨?_, Or.inr ⟨t, ch, ?_, Or.inr (Or.inl h2)⟩⟩)
              · simp [NetworkState.applyAdv, FixedPart.address_eq,
                  Adjudicator.finalizedWith_channel, Adjudicator.tick_statusOf, hst,
                  ChannelStatus.finalizedWith_challenged, hexp2]
              · simpa [NetworkState.applyAdv, Adjudicator.tick_statusOf] using hst
          · have hdl : net1.chain.now + dt < ch.deadline := by
              have := hboundM
              simpa [NetworkState.applyAdv, Adjudicator.tick_now] using lt_of_le_of_lt this hddC
            refine Or.inr (Or.inr ⟨?_, Or.inr ⟨t, ch, ?_, Or.inr (Or.inr ⟨hltC, hddC⟩)⟩⟩)
            · simp [NetworkState.applyAdv, FixedPart.address_eq,
                Adjudicator.finalizedWith_channel, Adjudicator.tick_statusOf, hst,
                ChannelStatus.finalizedWith_challenged, not_le.mpr hdl]
            · simpa [NetworkState.applyAdv, Adjudicator.tick_statusOf] using hst
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
    have hboundM : (net1.applyAdv apps m).chain.now ≤ net2.chain.now := hrest.now_le
    have hsupp : ∀ (proof : SupportProof E) (cand : State E),
        (∀ u ∈ proof, p ∈ u.signers → ∃ x ∈ net1.sent, x.state = u.state) →
        (apps c.appDef).supports c proof cand = true →
        (cand.turnNum < ss.state.turnNum ∨ cand = ss.state ∨ cand.outcome = Ω2) ∧
        (cand.isFinal = true → cand.outcome = Ω1 ∨ cand.outcome = Ω2) := by
      intro proof cand hUl hs
      rw [hc] at hs
      match proof, hs with
      | [u], hs =>
        simp only [consensusRules, Bool.and_eq_true, decide_eq_true_eq] at hs
        obtain ⟨⟨hus, huc⟩, hall'⟩ := hs
        obtain ⟨x, hx, hxs⟩ := hUl u (List.mem_singleton_self _) (hall' p (huc ▸ hp))
        have hb := hsent x hx (by rw [hxs]; exact huc)
        rw [hxs, hus] at hb
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
        | none => simpa using hf
        | some s' => exact Adjudicator.finalizedWith_apply h hf
    have hconclude : ∀ (caller : Participant) (ss' : SignedState E) (s' : Adjudicator E),
        T.feasible net1 (.chain caller (.conclude c ss')) →
        net1.chain.apply apps caller (.conclude c ss') = some s' →
        s'.finalizedWith c.address = some Ω1 ∨ s'.finalizedWith c.address = some Ω2 := by
      intro caller ss' s' hfeas' h
      obtain ⟨⟨-, hproof'⟩, rfl⟩ := Adjudicator.conclude_some h
      have hp' : p ∈ ss'.signers := hproof'.2.2 p (hproof'.1 ▸ hp)
      have hmem : ss' ∈ (Op.conclude c ss').proofStates := by simp [Op.proofStates]
      obtain ⟨x, hxmem, hxeq⟩ :=
        (hbounds.unforgeable net1 caller (.conclude c ss') hfeas' ss' hmem).1 hp'
      have hΩ' := (hsent x hxmem (by rw [hxeq]; exact hproof'.1)).2 (by rw [hxeq]; exact hproof'.2.1)
      rw [hxeq] at hΩ'
      rcases hΩ' with h1 | h2
      · exact Or.inl (by
          simp [FixedPart.address_eq, Adjudicator.finalizedWith_channel,
            Adjudicator.statusOf_setStatus, h1])
      · exact Or.inr (by
          simp [FixedPart.address_eq, Adjudicator.finalizedWith_channel,
            Adjudicator.statusOf_setStatus, h2])
    have hcheckpoint : ∀ (proof : SupportProof E) (cand : State E) (s' : Adjudicator E),
        net1.chain.checkpoint apps c proof cand = some s' →
        ∃ t', s'.statusOf c = .open t' ∧ s'.finalizedWith c.address = none := by
      intro proof cand s' h
      obtain ⟨-, rfl⟩ := Adjudicator.checkpoint_some h
      refine ⟨cand.turnNum, by rw [Adjudicator.statusOf_setStatus, if_pos rfl], ?_⟩
      simp [FixedPart.address_eq, Adjudicator.finalizedWith_channel, Adjudicator.statusOf_setStatus]
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
      have hpos : 0 < c.challengeDuration := lt_of_lt_of_le T.ε_pos (le_trans hself0 hdur)
      refine Or.inr (Or.inr ⟨?_, cand.turnNum,
        ⟨cand, net1.chain.now + c.challengeDuration⟩, ?_, ?_⟩)
      · simp [FixedPart.address_eq, Adjudicator.finalizedWith_channel,
          Adjudicator.statusOf_setStatus, ChannelStatus.finalizedWith_challenged,
          not_le.mpr (Nat.lt_add_of_pos_right hpos)]
      · simp [Adjudicator.statusOf_setStatus]
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
            have hge : T.ε ≤ c.challengeDuration := le_trans hself hdur
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
                  simp [FixedPart.address_eq, Adjudicator.finalizedWith_channel, hstatusc'],
                  Or.inl ⟨t, hstatusc'⟩⟩)
              | tick dt =>
                have hs' : net1.chain.tick dt = s' := by simpa using h
                subst hs'
                have hstatusc' : (net1.chain.tick dt).statusOf c = .open t := by
                  rw [Adjudicator.tick_statusOf]; exact ho
                exact Or.inr (Or.inr ⟨by
                  simp [FixedPart.address_eq, Adjudicator.finalizedWith_channel, hstatusc'],
                  Or.inl ⟨t, hstatusc'⟩⟩)
              | transfer a b =>
                by_cases hac : a = c
                · subst hac
                  obtain ⟨o, -, -, hfo, -, -, -, -, -, -, -, -⟩ := Adjudicator.transfer_some h
                  rw [hfo1] at hfo; exact absurd hfo (by simp)
                · obtain ⟨_, _, _, _, _, _, _, _, hs, _, _, _⟩ := Adjudicator.transfer_some h
                  have hstatusc' : s'.statusOf c = .open t := by
                    rw [Adjudicator.statusOf_of_status hs, Adjudicator.statusOf_setStatus,
                      if_neg (Ne.symm hac)]
                    exact ho
                  exact Or.inr (Or.inr ⟨by
                    simp [FixedPart.address_eq, Adjudicator.finalizedWith_channel, hstatusc'],
                    Or.inl ⟨t, hstatusc'⟩⟩)
              | reclaim l v =>
                by_cases hlc : l = c
                · subst hlc
                  obtain ⟨oL, -, -, -, -, hfo, -, -, -, -, -, -, -, -⟩ := Adjudicator.reclaim_some h
                  rw [hfo1] at hfo; exact absurd hfo (by simp)
                · obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hs', _, _⟩ := Adjudicator.reclaim_some h
                  have hstatusc' : s'.statusOf c = .open t := by
                    rw [hs', Adjudicator.statusOf_setStatus, if_neg (Ne.symm hlc)]
                    exact ho
                  exact Or.inr (Or.inr ⟨by
                    simp [FixedPart.address_eq, Adjudicator.finalizedWith_channel, hstatusc'],
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
                    simp [FixedPart.address_eq, Adjudicator.finalizedWith_channel, hstatusc'],
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
                    simp [FixedPart.address_eq, Adjudicator.finalizedWith_channel, hstatusc'],
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
                    simp [FixedPart.address_eq, Adjudicator.finalizedWith_channel, hstatusc'],
                    Or.inl ⟨t, hstatusc'⟩⟩)
        · have hnotexp : ¬ ch.deadline ≤ net1.chain.now := by
            intro hle
            have hcontra : net1.chain.finalizedWith c.address = some ch.state.outcome := by
              simp [FixedPart.address_eq, Adjudicator.finalizedWith_channel, hst,
                ChannelStatus.finalizedWith_challenged, hle]
            rw [hfn] at hcontra; exact absurd hcontra (by simp)
          have hfo1 : net1.chain.finalOutcome c.address = none := by
            simp [FixedPart.address_eq, Adjudicator.finalOutcome_channel, hst,
              ChannelStatus.finalOutcome_challenged, hnotexp]
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
                    simp [FixedPart.address_eq, Adjudicator.finalizedWith_channel, hstatusc', hn,
                      ChannelStatus.finalizedWith_challenged, hnotexp],
                    Or.inr ⟨t, ch, hstatusc', Or.inl h1⟩⟩)
                | tick dt =>
                  have hs' : net1.chain.tick dt = s' := by simpa using h
                  subst hs'
                  by_cases hexp2 : ch.deadline ≤ net1.chain.now + dt
                  · exact Or.inl (by
                      simp [FixedPart.address_eq, Adjudicator.finalizedWith_channel,
                        Adjudicator.tick_statusOf, hst, ChannelStatus.finalizedWith_challenged,
                        hexp2, h1])
                  · refine Or.inr (Or.inr ⟨?_, Or.inr ⟨t, ch, ?_, Or.inl h1⟩⟩)
                    · simp [FixedPart.address_eq, Adjudicator.finalizedWith_channel,
                        Adjudicator.tick_statusOf, hst, ChannelStatus.finalizedWith_challenged,
                        hexp2]
                    · rw [Adjudicator.tick_statusOf]; exact hst
                | transfer a b =>
                  by_cases hac : a = c
                  · subst hac
                    obtain ⟨o, -, -, hfo, -, -, -, -, -, -, -, -⟩ := Adjudicator.transfer_some h
                    rw [hfo1] at hfo; exact absurd hfo (by simp)
                  · obtain ⟨_, _, _, _, _, _, _, _, hs, hn, _, _⟩ := Adjudicator.transfer_some h
                    have hstatusc' : s'.statusOf c = .challenged t ch := by
                      rw [Adjudicator.statusOf_of_status hs, Adjudicator.statusOf_setStatus,
                        if_neg (Ne.symm hac)]
                      exact hst
                    exact Or.inr (Or.inr ⟨by
                      simp [FixedPart.address_eq, Adjudicator.finalizedWith_channel, hstatusc', hn,
                        ChannelStatus.finalizedWith_challenged, hnotexp],
                      Or.inr ⟨t, ch, hstatusc', Or.inl h1⟩⟩)
                | reclaim l v =>
                  by_cases hlc : l = c
                  · subst hlc
                    obtain ⟨oL, -, -, -, -, hfo, -, -, -, -, -, -, -, -⟩ := Adjudicator.reclaim_some h
                    rw [hfo1] at hfo; exact absurd hfo (by simp)
                  · obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hs', _, _⟩ := Adjudicator.reclaim_some h
                    have hstatusc' : s'.statusOf c = .challenged t ch := by
                      rw [hs', Adjudicator.statusOf_setStatus, if_neg (Ne.symm hlc)]
                      exact hst
                    have hn : s'.now = net1.chain.now := by
                      rw [hs']; exact Adjudicator.setStatus_now _ _ _
                    exact Or.inr (Or.inr ⟨by
                      simp [FixedPart.address_eq, Adjudicator.finalizedWith_channel, hstatusc', hn,
                        ChannelStatus.finalizedWith_challenged, hnotexp],
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
                      simp [FixedPart.address_eq, Adjudicator.finalizedWith_channel, hstatusc', hn,
                        ChannelStatus.finalizedWith_challenged, hnotexp],
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
                      simp [FixedPart.address_eq, Adjudicator.finalizedWith_channel, hstatusc', hn,
                        ChannelStatus.finalizedWith_challenged, hnotexp],
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
                      simp [FixedPart.address_eq, Adjudicator.finalizedWith_channel, hstatusc', hn,
                        ChannelStatus.finalizedWith_challenged, hnotexp],
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
                    simp [FixedPart.address_eq, Adjudicator.finalizedWith_channel, hstatusc', hn,
                      ChannelStatus.finalizedWith_challenged, hnotexp],
                    Or.inr ⟨t, ch, hstatusc', Or.inr (Or.inl h2)⟩⟩)
                | tick dt =>
                  have hs' : net1.chain.tick dt = s' := by simpa using h
                  subst hs'
                  by_cases hexp2 : ch.deadline ≤ net1.chain.now + dt
                  · exact Or.inr (Or.inl (by
                      simp [FixedPart.address_eq, Adjudicator.finalizedWith_channel,
                        Adjudicator.tick_statusOf, hst, ChannelStatus.finalizedWith_challenged,
                        hexp2, h2]))
                  · refine Or.inr (Or.inr ⟨?_, Or.inr ⟨t, ch, ?_, Or.inr (Or.inl h2)⟩⟩)
                    · simp [FixedPart.address_eq, Adjudicator.finalizedWith_channel,
                        Adjudicator.tick_statusOf, hst, ChannelStatus.finalizedWith_challenged,
                        hexp2]
                    · rw [Adjudicator.tick_statusOf]; exact hst
                | transfer a b =>
                  by_cases hac : a = c
                  · subst hac
                    obtain ⟨o, -, -, hfo, -, -, -, -, -, -, -, -⟩ := Adjudicator.transfer_some h
                    rw [hfo1] at hfo; exact absurd hfo (by simp)
                  · obtain ⟨_, _, _, _, _, _, _, _, hs, hn, _, _⟩ := Adjudicator.transfer_some h
                    have hstatusc' : s'.statusOf c = .challenged t ch := by
                      rw [Adjudicator.statusOf_of_status hs, Adjudicator.statusOf_setStatus,
                        if_neg (Ne.symm hac)]
                      exact hst
                    exact Or.inr (Or.inr ⟨by
                      simp [FixedPart.address_eq, Adjudicator.finalizedWith_channel, hstatusc', hn,
                        ChannelStatus.finalizedWith_challenged, hnotexp],
                      Or.inr ⟨t, ch, hstatusc', Or.inr (Or.inl h2)⟩⟩)
                | reclaim l v =>
                  by_cases hlc : l = c
                  · subst hlc
                    obtain ⟨oL, -, -, -, -, hfo, -, -, -, -, -, -, -, -⟩ := Adjudicator.reclaim_some h
                    rw [hfo1] at hfo; exact absurd hfo (by simp)
                  · obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hs', _, _⟩ := Adjudicator.reclaim_some h
                    have hstatusc' : s'.statusOf c = .challenged t ch := by
                      rw [hs', Adjudicator.statusOf_setStatus, if_neg (Ne.symm hlc)]
                      exact hst
                    have hn : s'.now = net1.chain.now := by
                      rw [hs']; exact Adjudicator.setStatus_now _ _ _
                    exact Or.inr (Or.inr ⟨by
                      simp [FixedPart.address_eq, Adjudicator.finalizedWith_channel, hstatusc', hn,
                        ChannelStatus.finalizedWith_challenged, hnotexp],
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
                      simp [FixedPart.address_eq, Adjudicator.finalizedWith_channel, hstatusc', hn,
                        ChannelStatus.finalizedWith_challenged, hnotexp],
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
                      simp [FixedPart.address_eq, Adjudicator.finalizedWith_channel, hstatusc', hn,
                        ChannelStatus.finalizedWith_challenged, hnotexp],
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
                      simp [FixedPart.address_eq, Adjudicator.finalizedWith_channel, hstatusc', hn,
                        ChannelStatus.finalizedWith_challenged, hnotexp],
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
                  have := hboundM; simpa [NetworkState.applyAdv, h] using lt_of_le_of_lt this hddC
                cases op with
                | deposit a e x =>
                  obtain ⟨-, -, -, -, hs, -⟩ := Adjudicator.deposit_some h
                  have hstatusc' : s'.statusOf c = .challenged t ch := by
                    rw [Adjudicator.statusOf_of_status hs]; exact hst
                  exact Or.inr (Or.inr ⟨by
                    simp [FixedPart.address_eq, Adjudicator.finalizedWith_channel, hstatusc',
                      ChannelStatus.finalizedWith_challenged, not_le.mpr hdl],
                    Or.inr ⟨t, ch, hstatusc', Or.inr (Or.inr ⟨hltC, hddC⟩)⟩⟩)
                | tick dt =>
                  have hs' : net1.chain.tick dt = s' := by simpa using h
                  subst hs'
                  have hdl' : net1.chain.now + dt < ch.deadline := by
                    simpa [Adjudicator.tick_now] using hdl
                  refine Or.inr (Or.inr ⟨?_, Or.inr ⟨t, ch, ?_, Or.inr (Or.inr ⟨hltC, hddC⟩)⟩⟩)
                  · simp [FixedPart.address_eq, Adjudicator.finalizedWith_channel,
                      Adjudicator.tick_statusOf, hst, ChannelStatus.finalizedWith_challenged,
                      not_le.mpr hdl']
                  · rw [Adjudicator.tick_statusOf]; exact hst
                | transfer a b =>
                  by_cases hac : a = c
                  · subst hac
                    obtain ⟨o, -, -, hfo, -, -, -, -, -, -, -, -⟩ := Adjudicator.transfer_some h
                    rw [hfo1] at hfo; exact absurd hfo (by simp)
                  · obtain ⟨_, _, _, _, _, _, _, _, hs, _, _, _⟩ := Adjudicator.transfer_some h
                    have hstatusc' : s'.statusOf c = .challenged t ch := by
                      rw [Adjudicator.statusOf_of_status hs, Adjudicator.statusOf_setStatus,
                        if_neg (Ne.symm hac)]
                      exact hst
                    exact Or.inr (Or.inr ⟨by
                      simp [FixedPart.address_eq, Adjudicator.finalizedWith_channel, hstatusc',
                        ChannelStatus.finalizedWith_challenged, not_le.mpr hdl],
                      Or.inr ⟨t, ch, hstatusc', Or.inr (Or.inr ⟨hltC, hddC⟩)⟩⟩)
                | reclaim l v =>
                  by_cases hlc : l = c
                  · subst hlc
                    obtain ⟨oL, -, -, -, -, hfo, -, -, -, -, -, -, -, -⟩ := Adjudicator.reclaim_some h
                    rw [hfo1] at hfo; exact absurd hfo (by simp)
                  · obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hs', _, _⟩ := Adjudicator.reclaim_some h
                    have hstatusc' : s'.statusOf c = .challenged t ch := by
                      rw [hs', Adjudicator.statusOf_setStatus, if_neg (Ne.symm hlc)]
                      exact hst
                    exact Or.inr (Or.inr ⟨by
                      simp [FixedPart.address_eq, Adjudicator.finalizedWith_channel, hstatusc',
                        ChannelStatus.finalizedWith_challenged, not_le.mpr hdl],
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
                      simp [FixedPart.address_eq, Adjudicator.finalizedWith_channel, hstatusc',
                        ChannelStatus.finalizedWith_challenged, not_le.mpr hdl],
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
                      simp [FixedPart.address_eq, Adjudicator.finalizedWith_channel, hstatusc',
                        ChannelStatus.finalizedWith_challenged, not_le.mpr hdl],
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
                      simp [FixedPart.address_eq, Adjudicator.finalizedWith_channel, hstatusc',
                        ChannelStatus.finalizedWith_challenged, not_le.mpr hdl],
                      Or.inr ⟨t, ch, hstatusc', Or.inr (Or.inr ⟨hltC, hddC⟩)⟩⟩)
    have hbase' := step hbase
    have hεbound' : net2.chain.now < (net1.applyAdv apps m).chain.now + T.ε :=
      lt_of_lt_of_le hεbound (Nat.add_le_add_right (NetworkState.applyAdv_now_le apps net1 m) T.ε)
    have hsent' : ∀ t0 ∈ (net1.applyAdv apps m).sent, t0.state.channel = c →
        (t0.state.turnNum < ss.state.turnNum ∨ t0.state = ss.state ∨ t0.state.outcome = Ω2) ∧
        (t0.state.isFinal = true → t0.state.outcome = Ω1 ∨ t0.state.outcome = Ω2) := by
      rw [NetworkState.applyAdv_sent]; exact hsent
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
    (hc : apps c.appDef = consensusRules) (hp : p ∈ c.participants) (hΩ1 : ss.state.outcome = Ω1)
    (hdur : 2 * T.ε ≤ c.challengeDuration) {net net' : NetworkState E p} (t : Time)
    (ht : t = net.chain.now)
    (hseq : Threat.RoundSeq apps T t [Op.checkpoint c [ss] ss.state] net net') :
    net'.chain.now < net.chain.now + T.ε →
    (∀ t0 ∈ net.sent, t0.state.channel = c →
      (t0.state.turnNum < ss.state.turnNum ∨ t0.state = ss.state ∨ t0.state.outcome = Ω2) ∧
      (t0.state.isFinal = true → t0.state.outcome = Ω1 ∨ t0.state.outcome = Ω2)) →
    ConsensusSafe c ss Ω1 Ω2 net net' → ConsensusSafe c ss Ω1 Ω2 net' net' := by
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
          | none => simpa [NetworkState.applyAdv, hop] using hbase
          | some s' =>
            obtain ⟨⟨-, -, -, -⟩, hseq'⟩ := Adjudicator.checkpoint_some hop
            refine Or.inr (Or.inr ⟨?_, Or.inl ⟨ss.state.turnNum, ?_⟩⟩)
            · simp [NetworkState.applyAdv, hop, hseq', FixedPart.address_eq,
                Adjudicator.finalizedWith_channel, Adjudicator.statusOf_setStatus]
            · simp [NetworkState.applyAdv, hop, hseq', Adjudicator.statusOf_setStatus]
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
        exact consensus_round_safe_nil hbounds hc hp hΩ1 hdur hrest hεbound' hsent_land hbase_land
      · simp at hsplit
    · simp at hsplit
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
              .open t := by simpa [NetworkState.applyAdv] using ho
          exact Or.inr (Or.inr ⟨by
            simp [FixedPart.address_eq, Adjudicator.finalizedWith_channel, hstatusc'],
            Or.inl ⟨t, hstatusc'⟩⟩)
        · have hnotexp : ¬ ch.deadline ≤ net1.chain.now := by
            intro hle
            have hcontra : net1.chain.finalizedWith c.address = some ch.state.outcome := by
              simp [FixedPart.address_eq, Adjudicator.finalizedWith_channel, hst,
                ChannelStatus.finalizedWith_challenged, hle]
            rw [hfn] at hcontra; exact absurd hcontra (by simp)
          rcases hdisj with h1 | h2 | ⟨hltC, hddC⟩
          · by_cases hexp2 : ch.deadline ≤ net1.chain.now + dt
            · exact Or.inl (by
                simp [NetworkState.applyAdv, FixedPart.address_eq,
                  Adjudicator.finalizedWith_channel, Adjudicator.tick_statusOf, hst,
                  ChannelStatus.finalizedWith_challenged, hexp2, h1])
            · refine Or.inr (Or.inr ⟨?_, Or.inr ⟨t, ch, ?_, Or.inl h1⟩⟩)
              · simp [NetworkState.applyAdv, FixedPart.address_eq,
                  Adjudicator.finalizedWith_channel, Adjudicator.tick_statusOf, hst,
                  ChannelStatus.finalizedWith_challenged, hexp2]
              · simpa [NetworkState.applyAdv, Adjudicator.tick_statusOf] using hst
          · by_cases hexp2 : ch.deadline ≤ net1.chain.now + dt
            · exact Or.inr (Or.inl (by
                simp [NetworkState.applyAdv, FixedPart.address_eq,
                  Adjudicator.finalizedWith_channel, Adjudicator.tick_statusOf, hst,
                  ChannelStatus.finalizedWith_challenged, hexp2, h2]))
            · refine Or.inr (Or.inr ⟨?_, Or.inr ⟨t, ch, ?_, Or.inr (Or.inl h2)⟩⟩)
              · simp [NetworkState.applyAdv, FixedPart.address_eq,
                  Adjudicator.finalizedWith_channel, Adjudicator.tick_statusOf, hst,
                  ChannelStatus.finalizedWith_challenged, hexp2]
              · simpa [NetworkState.applyAdv, Adjudicator.tick_statusOf] using hst
          · have hdl : net1.chain.now + dt < ch.deadline := by
              have := hboundM
              simpa [NetworkState.applyAdv, Adjudicator.tick_now] using lt_of_le_of_lt this hddC
            refine Or.inr (Or.inr ⟨?_, Or.inr ⟨t, ch, ?_, Or.inr (Or.inr ⟨hltC, hddC⟩)⟩⟩)
            · simp [NetworkState.applyAdv, FixedPart.address_eq,
                Adjudicator.finalizedWith_channel, Adjudicator.tick_statusOf, hst,
                ChannelStatus.finalizedWith_challenged, not_le.mpr hdl]
            · simpa [NetworkState.applyAdv, Adjudicator.tick_statusOf] using hst
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
    have hboundM : (net1.applyAdv apps m).chain.now ≤ net2.chain.now := hrest.now_le
    have hsupp : ∀ (proof : SupportProof E) (cand : State E),
        (∀ u ∈ proof, p ∈ u.signers → ∃ x ∈ net1.sent, x.state = u.state) →
        (apps c.appDef).supports c proof cand = true →
        (cand.turnNum < ss.state.turnNum ∨ cand = ss.state ∨ cand.outcome = Ω2) ∧
        (cand.isFinal = true → cand.outcome = Ω1 ∨ cand.outcome = Ω2) := by
      intro proof cand hUl hs
      rw [hc] at hs
      match proof, hs with
      | [u], hs =>
        simp only [consensusRules, Bool.and_eq_true, decide_eq_true_eq] at hs
        obtain ⟨⟨hus, huc⟩, hall'⟩ := hs
        obtain ⟨x, hx, hxs⟩ := hUl u (List.mem_singleton_self _) (hall' p (huc ▸ hp))
        have hb := hsent x hx (by rw [hxs]; exact huc)
        rw [hxs, hus] at hb
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
        | none => simpa using hf
        | some s' => exact Adjudicator.finalizedWith_apply h hf
    have hconclude : ∀ (caller : Participant) (ss' : SignedState E) (s' : Adjudicator E),
        T.feasible net1 (.chain caller (.conclude c ss')) →
        net1.chain.apply apps caller (.conclude c ss') = some s' →
        s'.finalizedWith c.address = some Ω1 ∨ s'.finalizedWith c.address = some Ω2 := by
      intro caller ss' s' hfeas' h
      obtain ⟨⟨-, hproof'⟩, rfl⟩ := Adjudicator.conclude_some h
      have hp' : p ∈ ss'.signers := hproof'.2.2 p (hproof'.1 ▸ hp)
      have hmem : ss' ∈ (Op.conclude c ss').proofStates := by simp [Op.proofStates]
      obtain ⟨x, hxmem, hxeq⟩ :=
        (hbounds.unforgeable net1 caller (.conclude c ss') hfeas' ss' hmem).1 hp'
      have hΩ' := (hsent x hxmem (by rw [hxeq]; exact hproof'.1)).2 (by rw [hxeq]; exact hproof'.2.1)
      rw [hxeq] at hΩ'
      rcases hΩ' with h1 | h2
      · exact Or.inl (by
          simp [FixedPart.address_eq, Adjudicator.finalizedWith_channel,
            Adjudicator.statusOf_setStatus, h1])
      · exact Or.inr (by
          simp [FixedPart.address_eq, Adjudicator.finalizedWith_channel,
            Adjudicator.statusOf_setStatus, h2])
    have hcheckpoint : ∀ (proof : SupportProof E) (cand : State E) (s' : Adjudicator E),
        net1.chain.checkpoint apps c proof cand = some s' →
        ∃ t', s'.statusOf c = .open t' ∧ s'.finalizedWith c.address = none := by
      intro proof cand s' h
      obtain ⟨-, rfl⟩ := Adjudicator.checkpoint_some h
      refine ⟨cand.turnNum, by rw [Adjudicator.statusOf_setStatus, if_pos rfl], ?_⟩
      simp [FixedPart.address_eq, Adjudicator.finalizedWith_channel, Adjudicator.statusOf_setStatus]
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
      have hpos : 0 < c.challengeDuration := lt_of_lt_of_le T.ε_pos (le_trans hself0 hdur)
      refine Or.inr (Or.inr ⟨?_, cand.turnNum,
        ⟨cand, net1.chain.now + c.challengeDuration⟩, ?_, ?_⟩)
      · simp [FixedPart.address_eq, Adjudicator.finalizedWith_channel,
          Adjudicator.statusOf_setStatus, ChannelStatus.finalizedWith_challenged,
          not_le.mpr (Nat.lt_add_of_pos_right hpos)]
      · simp [Adjudicator.statusOf_setStatus]
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
            have hge : T.ε ≤ c.challengeDuration := le_trans hself hdur
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
                  simp [FixedPart.address_eq, Adjudicator.finalizedWith_channel, hstatusc'],
                  Or.inl ⟨t, hstatusc'⟩⟩)
              | tick dt =>
                have hs' : net1.chain.tick dt = s' := by simpa using h
                subst hs'
                have hstatusc' : (net1.chain.tick dt).statusOf c = .open t := by
                  rw [Adjudicator.tick_statusOf]; exact ho
                exact Or.inr (Or.inr ⟨by
                  simp [FixedPart.address_eq, Adjudicator.finalizedWith_channel, hstatusc'],
                  Or.inl ⟨t, hstatusc'⟩⟩)
              | transfer a b =>
                by_cases hac : a = c
                · subst hac
                  obtain ⟨o, -, -, hfo, -, -, -, -, -, -, -, -⟩ := Adjudicator.transfer_some h
                  rw [hfo1] at hfo; exact absurd hfo (by simp)
                · obtain ⟨_, _, _, _, _, _, _, _, hs, _, _, _⟩ := Adjudicator.transfer_some h
                  have hstatusc' : s'.statusOf c = .open t := by
                    rw [Adjudicator.statusOf_of_status hs, Adjudicator.statusOf_setStatus,
                      if_neg (Ne.symm hac)]
                    exact ho
                  exact Or.inr (Or.inr ⟨by
                    simp [FixedPart.address_eq, Adjudicator.finalizedWith_channel, hstatusc'],
                    Or.inl ⟨t, hstatusc'⟩⟩)
              | reclaim l v =>
                by_cases hlc : l = c
                · subst hlc
                  obtain ⟨oL, -, -, -, -, hfo, -, -, -, -, -, -, -, -⟩ := Adjudicator.reclaim_some h
                  rw [hfo1] at hfo; exact absurd hfo (by simp)
                · obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hs', _, _⟩ := Adjudicator.reclaim_some h
                  have hstatusc' : s'.statusOf c = .open t := by
                    rw [hs', Adjudicator.statusOf_setStatus, if_neg (Ne.symm hlc)]
                    exact ho
                  exact Or.inr (Or.inr ⟨by
                    simp [FixedPart.address_eq, Adjudicator.finalizedWith_channel, hstatusc'],
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
                    simp [FixedPart.address_eq, Adjudicator.finalizedWith_channel, hstatusc'],
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
                    simp [FixedPart.address_eq, Adjudicator.finalizedWith_channel, hstatusc'],
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
                    simp [FixedPart.address_eq, Adjudicator.finalizedWith_channel, hstatusc'],
                    Or.inl ⟨t, hstatusc'⟩⟩)
        · have hnotexp : ¬ ch.deadline ≤ net1.chain.now := by
            intro hle
            have hcontra : net1.chain.finalizedWith c.address = some ch.state.outcome := by
              simp [FixedPart.address_eq, Adjudicator.finalizedWith_channel, hst,
                ChannelStatus.finalizedWith_challenged, hle]
            rw [hfn] at hcontra; exact absurd hcontra (by simp)
          have hfo1 : net1.chain.finalOutcome c.address = none := by
            simp [FixedPart.address_eq, Adjudicator.finalOutcome_channel, hst,
              ChannelStatus.finalOutcome_challenged, hnotexp]
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
                    simp [FixedPart.address_eq, Adjudicator.finalizedWith_channel, hstatusc', hn,
                      ChannelStatus.finalizedWith_challenged, hnotexp],
                    Or.inr ⟨t, ch, hstatusc', Or.inl h1⟩⟩)
                | tick dt =>
                  have hs' : net1.chain.tick dt = s' := by simpa using h
                  subst hs'
                  by_cases hexp2 : ch.deadline ≤ net1.chain.now + dt
                  · exact Or.inl (by
                      simp [FixedPart.address_eq, Adjudicator.finalizedWith_channel,
                        Adjudicator.tick_statusOf, hst, ChannelStatus.finalizedWith_challenged,
                        hexp2, h1])
                  · refine Or.inr (Or.inr ⟨?_, Or.inr ⟨t, ch, ?_, Or.inl h1⟩⟩)
                    · simp [FixedPart.address_eq, Adjudicator.finalizedWith_channel,
                        Adjudicator.tick_statusOf, hst, ChannelStatus.finalizedWith_challenged,
                        hexp2]
                    · rw [Adjudicator.tick_statusOf]; exact hst
                | transfer a b =>
                  by_cases hac : a = c
                  · subst hac
                    obtain ⟨o, -, -, hfo, -, -, -, -, -, -, -, -⟩ := Adjudicator.transfer_some h
                    rw [hfo1] at hfo; exact absurd hfo (by simp)
                  · obtain ⟨_, _, _, _, _, _, _, _, hs, hn, _, _⟩ := Adjudicator.transfer_some h
                    have hstatusc' : s'.statusOf c = .challenged t ch := by
                      rw [Adjudicator.statusOf_of_status hs, Adjudicator.statusOf_setStatus,
                        if_neg (Ne.symm hac)]
                      exact hst
                    exact Or.inr (Or.inr ⟨by
                      simp [FixedPart.address_eq, Adjudicator.finalizedWith_channel, hstatusc', hn,
                        ChannelStatus.finalizedWith_challenged, hnotexp],
                      Or.inr ⟨t, ch, hstatusc', Or.inl h1⟩⟩)
                | reclaim l v =>
                  by_cases hlc : l = c
                  · subst hlc
                    obtain ⟨oL, -, -, -, -, hfo, -, -, -, -, -, -, -, -⟩ := Adjudicator.reclaim_some h
                    rw [hfo1] at hfo; exact absurd hfo (by simp)
                  · obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hs', _, _⟩ := Adjudicator.reclaim_some h
                    have hstatusc' : s'.statusOf c = .challenged t ch := by
                      rw [hs', Adjudicator.statusOf_setStatus, if_neg (Ne.symm hlc)]
                      exact hst
                    have hn : s'.now = net1.chain.now := by
                      rw [hs']; exact Adjudicator.setStatus_now _ _ _
                    exact Or.inr (Or.inr ⟨by
                      simp [FixedPart.address_eq, Adjudicator.finalizedWith_channel, hstatusc', hn,
                        ChannelStatus.finalizedWith_challenged, hnotexp],
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
                      simp [FixedPart.address_eq, Adjudicator.finalizedWith_channel, hstatusc', hn,
                        ChannelStatus.finalizedWith_challenged, hnotexp],
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
                      simp [FixedPart.address_eq, Adjudicator.finalizedWith_channel, hstatusc', hn,
                        ChannelStatus.finalizedWith_challenged, hnotexp],
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
                      simp [FixedPart.address_eq, Adjudicator.finalizedWith_channel, hstatusc', hn,
                        ChannelStatus.finalizedWith_challenged, hnotexp],
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
                    simp [FixedPart.address_eq, Adjudicator.finalizedWith_channel, hstatusc', hn,
                      ChannelStatus.finalizedWith_challenged, hnotexp],
                    Or.inr ⟨t, ch, hstatusc', Or.inr (Or.inl h2)⟩⟩)
                | tick dt =>
                  have hs' : net1.chain.tick dt = s' := by simpa using h
                  subst hs'
                  by_cases hexp2 : ch.deadline ≤ net1.chain.now + dt
                  · exact Or.inr (Or.inl (by
                      simp [FixedPart.address_eq, Adjudicator.finalizedWith_channel,
                        Adjudicator.tick_statusOf, hst, ChannelStatus.finalizedWith_challenged,
                        hexp2, h2]))
                  · refine Or.inr (Or.inr ⟨?_, Or.inr ⟨t, ch, ?_, Or.inr (Or.inl h2)⟩⟩)
                    · simp [FixedPart.address_eq, Adjudicator.finalizedWith_channel,
                        Adjudicator.tick_statusOf, hst, ChannelStatus.finalizedWith_challenged,
                        hexp2]
                    · rw [Adjudicator.tick_statusOf]; exact hst
                | transfer a b =>
                  by_cases hac : a = c
                  · subst hac
                    obtain ⟨o, -, -, hfo, -, -, -, -, -, -, -, -⟩ := Adjudicator.transfer_some h
                    rw [hfo1] at hfo; exact absurd hfo (by simp)
                  · obtain ⟨_, _, _, _, _, _, _, _, hs, hn, _, _⟩ := Adjudicator.transfer_some h
                    have hstatusc' : s'.statusOf c = .challenged t ch := by
                      rw [Adjudicator.statusOf_of_status hs, Adjudicator.statusOf_setStatus,
                        if_neg (Ne.symm hac)]
                      exact hst
                    exact Or.inr (Or.inr ⟨by
                      simp [FixedPart.address_eq, Adjudicator.finalizedWith_channel, hstatusc', hn,
                        ChannelStatus.finalizedWith_challenged, hnotexp],
                      Or.inr ⟨t, ch, hstatusc', Or.inr (Or.inl h2)⟩⟩)
                | reclaim l v =>
                  by_cases hlc : l = c
                  · subst hlc
                    obtain ⟨oL, -, -, -, -, hfo, -, -, -, -, -, -, -, -⟩ := Adjudicator.reclaim_some h
                    rw [hfo1] at hfo; exact absurd hfo (by simp)
                  · obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hs', _, _⟩ := Adjudicator.reclaim_some h
                    have hstatusc' : s'.statusOf c = .challenged t ch := by
                      rw [hs', Adjudicator.statusOf_setStatus, if_neg (Ne.symm hlc)]
                      exact hst
                    have hn : s'.now = net1.chain.now := by
                      rw [hs']; exact Adjudicator.setStatus_now _ _ _
                    exact Or.inr (Or.inr ⟨by
                      simp [FixedPart.address_eq, Adjudicator.finalizedWith_channel, hstatusc', hn,
                        ChannelStatus.finalizedWith_challenged, hnotexp],
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
                      simp [FixedPart.address_eq, Adjudicator.finalizedWith_channel, hstatusc', hn,
                        ChannelStatus.finalizedWith_challenged, hnotexp],
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
                      simp [FixedPart.address_eq, Adjudicator.finalizedWith_channel, hstatusc', hn,
                        ChannelStatus.finalizedWith_challenged, hnotexp],
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
                      simp [FixedPart.address_eq, Adjudicator.finalizedWith_channel, hstatusc', hn,
                        ChannelStatus.finalizedWith_challenged, hnotexp],
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
                  have := hboundM; simpa [NetworkState.applyAdv, h] using lt_of_le_of_lt this hddC
                cases op with
                | deposit a e x =>
                  obtain ⟨-, -, -, -, hs, -⟩ := Adjudicator.deposit_some h
                  have hstatusc' : s'.statusOf c = .challenged t ch := by
                    rw [Adjudicator.statusOf_of_status hs]; exact hst
                  exact Or.inr (Or.inr ⟨by
                    simp [FixedPart.address_eq, Adjudicator.finalizedWith_channel, hstatusc',
                      ChannelStatus.finalizedWith_challenged, not_le.mpr hdl],
                    Or.inr ⟨t, ch, hstatusc', Or.inr (Or.inr ⟨hltC, hddC⟩)⟩⟩)
                | tick dt =>
                  have hs' : net1.chain.tick dt = s' := by simpa using h
                  subst hs'
                  have hdl' : net1.chain.now + dt < ch.deadline := by
                    simpa [Adjudicator.tick_now] using hdl
                  refine Or.inr (Or.inr ⟨?_, Or.inr ⟨t, ch, ?_, Or.inr (Or.inr ⟨hltC, hddC⟩)⟩⟩)
                  · simp [FixedPart.address_eq, Adjudicator.finalizedWith_channel,
                      Adjudicator.tick_statusOf, hst, ChannelStatus.finalizedWith_challenged,
                      not_le.mpr hdl']
                  · rw [Adjudicator.tick_statusOf]; exact hst
                | transfer a b =>
                  by_cases hac : a = c
                  · subst hac
                    obtain ⟨o, -, -, hfo, -, -, -, -, -, -, -, -⟩ := Adjudicator.transfer_some h
                    rw [hfo1] at hfo; exact absurd hfo (by simp)
                  · obtain ⟨_, _, _, _, _, _, _, _, hs, _, _, _⟩ := Adjudicator.transfer_some h
                    have hstatusc' : s'.statusOf c = .challenged t ch := by
                      rw [Adjudicator.statusOf_of_status hs, Adjudicator.statusOf_setStatus,
                        if_neg (Ne.symm hac)]
                      exact hst
                    exact Or.inr (Or.inr ⟨by
                      simp [FixedPart.address_eq, Adjudicator.finalizedWith_channel, hstatusc',
                        ChannelStatus.finalizedWith_challenged, not_le.mpr hdl],
                      Or.inr ⟨t, ch, hstatusc', Or.inr (Or.inr ⟨hltC, hddC⟩)⟩⟩)
                | reclaim l v =>
                  by_cases hlc : l = c
                  · subst hlc
                    obtain ⟨oL, -, -, -, -, hfo, -, -, -, -, -, -, -, -⟩ := Adjudicator.reclaim_some h
                    rw [hfo1] at hfo; exact absurd hfo (by simp)
                  · obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hs', _, _⟩ := Adjudicator.reclaim_some h
                    have hstatusc' : s'.statusOf c = .challenged t ch := by
                      rw [hs', Adjudicator.statusOf_setStatus, if_neg (Ne.symm hlc)]
                      exact hst
                    exact Or.inr (Or.inr ⟨by
                      simp [FixedPart.address_eq, Adjudicator.finalizedWith_channel, hstatusc',
                        ChannelStatus.finalizedWith_challenged, not_le.mpr hdl],
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
                      simp [FixedPart.address_eq, Adjudicator.finalizedWith_channel, hstatusc',
                        ChannelStatus.finalizedWith_challenged, not_le.mpr hdl],
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
                      simp [FixedPart.address_eq, Adjudicator.finalizedWith_channel, hstatusc',
                        ChannelStatus.finalizedWith_challenged, not_le.mpr hdl],
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
                      simp [FixedPart.address_eq, Adjudicator.finalizedWith_channel, hstatusc',
                        ChannelStatus.finalizedWith_challenged, not_le.mpr hdl],
                      Or.inr ⟨t, ch, hstatusc', Or.inr (Or.inr ⟨hltC, hddC⟩)⟩⟩)
    have hbase' := step hbase
    have hεbound' : net2.chain.now < (net1.applyAdv apps m).chain.now + T.ε :=
      lt_of_lt_of_le hεbound (Nat.add_le_add_right (NetworkState.applyAdv_now_le apps net1 m) T.ε)
    have hsent' : ∀ t0 ∈ (net1.applyAdv apps m).sent, t0.state.channel = c →
        (t0.state.turnNum < ss.state.turnNum ∨ t0.state = ss.state ∨ t0.state.outcome = Ω2) ∧
        (t0.state.isFinal = true → t0.state.outcome = Ω1 ∨ t0.state.outcome = Ω2) := by
      rw [NetworkState.applyAdv_sent]; exact hsent
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
  | land hsplit _ _ => rw [← hpnil] at hsplit; simp at hsplit
  | @tick pending net1 net2 dt hfeas hgate hrest ih =>
    intro hbase
    apply ih hpnil
    rcases hbase with hle | ⟨Ω, hΩ⟩
    · exact Or.inl (by simpa [NetworkState.applyAdv, Adjudicator.tick_statusOf] using hle)
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
      · exact Or.inl (by simpa [NetworkState.applyAdv] using hle)
      · exact Or.inr ⟨Ω, by simpa [NetworkState.applyAdv] using hΩ⟩
    | chain caller op =>
      simp only [NetworkState.applyAdv]
      cases h : net1.chain.apply apps caller op with
      | none =>
        rcases hbase with hle | ⟨Ω, hΩ⟩
        · exact Or.inl (by simpa [h] using hle)
        · exact Or.inr ⟨Ω, by simpa [h] using hΩ⟩
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
    {c : FixedPart} {ss : SignedState E} (hc : apps c.appDef = consensusRules)
    (hp : p ∈ c.participants) (hchan : ss.state.channel = c) (hall : ss.ByAll)
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
                  by rw [hc]; simp [consensusRules, hchan, hall], hchan, hlt0⟩
              have hop : net1.chain.apply apps p (Op.checkpoint c [ss] ss.state) =
                  some (net1.chain.setStatus c (.open ss.state.turnNum)) := by
                rw [Adjudicator.apply_checkpoint]; unfold Adjudicator.checkpoint
                rw [if_pos hcond]
              left
              simp [NetworkState.applyAdv, hop, Adjudicator.statusOf_setStatus]
          · cases hcc : net1.chain.apply apps p (Op.checkpoint c [ss] ss.state) with
            | none => left; simpa [NetworkState.applyAdv, hcc] using not_lt.mp hlt0
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
      · simp at hsplit
    · simp at hsplit
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
    (A : Assumptions apps p T) (net : NetworkState E p)
    (hr : (Nitro.participant apps T).Reachable net) (c : FixedPart) (ss : SignedState E)
    (Ω1 Ω2 : Outcome E) (hc : apps c.appDef = consensusRules) (hp : p ∈ c.participants)
    (hh : net.Holds ss) (hall : ss.ByAll) (hchan : ss.state.channel = c)
    (hΩ1 : ss.state.outcome = Ω1)
    (hsent : ∀ t ∈ net.sent, t.state.channel = c →
      (t.state.turnNum < ss.state.turnNum ∨ t.state = ss.state ∨ t.state.outcome = Ω2) ∧
      (t.state.isFinal = true → t.state.outcome = Ω1 ∨ t.state.outcome = Ω2))
    (hdur : 2 * T.ε ≤ c.challengeDuration)
    (hst : (∃ t, net.chain.statusOf c = .open t ∧ t ≤ ss.state.turnNum) ∨
      (∃ t ch, net.chain.statusOf c = .challenged t ch ∧
        (t < ss.state.turnNum ∨ ch.state = ss.state) ∧ net.chain.now + T.ε ≤ ch.deadline))
    (Ω : Outcome E) (hen : Enabled apps T c Ω net) : Ω = Ω1 ∨ Ω = Ω2 := by
  by_contra hΩne
  push Not at hΩne
  obtain ⟨hΩne1, hΩne2⟩ := hΩne
  have hen' : ¬ Prevents apps T (fun net' => net'.Finalized c Ω) net := hen
  apply hen'
  classical
  set σ : Strategy E p :=
    fun n => if n.Holds ss then HonestMove.chain (.checkpoint c [ss] ss.state) else .wait 0
    with hσdef
  have hfeas : ∀ n, (σ n).Feasible n := by
    intro n
    by_cases hn : n.Holds ss
    · rw [hσdef]; simp only [if_pos hn, HonestMove.Feasible_chain, Op.HonestFeasible,
        Op.proofStates, List.mem_singleton]
      intro ss' hss'; rw [hss']; exact hn
    · rw [hσdef]; simp [if_neg hn, HonestMove.Feasible]
  have hbase_net : ∀ {n2' : NetworkState E p}, n2'.chain.now < net.chain.now + T.ε →
      ConsensusSafe c ss Ω1 Ω2 net n2' := by
    intro n2' hlt
    rcases hst with ⟨t, ho, -⟩ | ⟨t, ch, hst', hdisj, hdd⟩
    · have hfz : net.chain.finalizedWith c.address = none := by
        simp [FixedPart.address_eq, Adjudicator.finalizedWith_channel, ho]
      exact Or.inr (Or.inr ⟨hfz, Or.inl ⟨t, ho⟩⟩)
    · have hεpos := T.ε_pos
      have hndl : net.chain.now < ch.deadline :=
        lt_of_lt_of_le (Nat.lt_add_of_pos_right hεpos) hdd
      have hfz : net.chain.finalizedWith c.address = none := by
        simp [FixedPart.address_eq, Adjudicator.finalizedWith_channel, hst',
          ChannelStatus.finalizedWith_challenged, not_le.mpr hndl]
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
        consensus_round_safe A.toBounds hc hp hΩ1 hdur n1'.chain.now rfl hseq hεbound hsentNow
          hsafeStart
      have hturn : ss.state.turnNum ≤ (n2.chain.statusOf c).turnNumRecord ∨
          ∃ Ω, n2.chain.finalizedWith c.address = some Ω :=
        consensus_checkpoint_resolves hc hp hchan hall n1'.chain.now rfl hseq
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
          · rw [hΩ'] at hfz; exact absurd hfz (by simp)
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
    consensus_round_safe A.toBounds hc hp hΩ1 hdur n1.chain.now rfl hseq hεbound hsentNow
      hsafeStart
  have hfin' : n2.chain.finalizedWith c.address = some Ω := hfin
  rcases hsafe2 with h1 | h2 | ⟨hfz, -⟩
  · exact hΩne1 (Option.some_inj.mp (hfin'.symm.trans h1))
  · exact hΩne2 (Option.some_inj.mp (hfin'.symm.trans h2))
  · rw [hfz] at hfin'; exact absurd hfin' (by simp)

/-- Nitro-30, Nitro-16. Nitro:775-777: "reasoning about redistribution is easy
    in Turbo: if you can find one strategy to move a certain amount into an
    address, then no-one else can prevent this from occurring." A transfer
    sequence that reaches balance `x` at the external destination `d` gives
    an unbeatable transfer-only strategy against a transfer-only adversary
    (Nitro:779-781). A channel target is excluded: the adversary can pay a
    finalized channel's coins onward in the same round. -/
theorem turbo_redistribution_unbeatable (apps : Apps E) {p : Participant} (T : Threat E p)
    (B : Bounds apps p T) (hT : T.TransfersOnly) (hcap : T.CapableTransfers)
    (net : NetworkState E p) (hr : (Nitro.participant apps T).Reachable net)
    (hdag : net.chain.IsDAG)
    (ops : List (Participant × Op E)) (hops : OnlyTransfers ops) (d : E) (x : Coins)
    (hgoal : x ≤ (Adjudicator.applyAll apps ops net.chain).balances.get (.external d)) :
    CanObtainIn apps T HonestMove.IsTransfer (.external d) x net := by
  sorry

/-- Nitro-31. Nitro:785-787: "a deposit into the system cannot reduce the value of
    any address and cannot increase the value of any address by more than the
    value of the deposit." -/
theorem deposit_bounds_value (apps : Apps E) {p : Participant} (T : Threat E p)
    (A : Assumptions apps p T) (net : NetworkState E p)
    (hr : (Nitro.participant apps T).Reachable net) (c : FixedPart) (d : E) (y x x' : Coins)
    (s' : Adjudicator E) (e : Coins) (hd : net.chain.deposit c.address e y = some s')
    (hv : Value apps T d net x) (hv' : Value apps T d { net with chain := s' } x') :
    x ≤ x' ∧ x' ≤ x + y := by
  sorry

/-- Nitro-31. Nitro:787-789: "Withdrawals can only occur from participant
    addresses and are the only way funds can leave these addresses, so cannot
    affect values elsewhere." go-nitro has no withdrawal: a payout is the
    transfer of a finalized entry to an external destination. A payout to
    another destination `q` leaves the value at `d` unchanged. -/
theorem payout_to_other_affects_only_owner (apps : Apps E) {p : Participant} (T : Threat E p)
    (A : Assumptions apps p T) (net : NetworkState E p)
    (hr : (Nitro.participant apps T).Reachable net) (d q : E) (hq : q ≠ d)
    (a : FixedPart) (s' : Adjudicator E) (h : net.chain.transfer a (.external q) = some s')
    (x : Coins) :
    Value apps T d net x ↔ Value apps T d { net with chain := s' } x := by
  sorry

/-- Under the consensus app, a channel's status never moves while its
    participant `p` has sent nothing: a successful `challenge`, `checkpoint`
    or `conclude` on `c` needs a state signed by every one of `c`'s
    participants (`consensusRules.supports`, `ConclusionProof`), so by
    `p ∈ c.participants` it needs `p`'s genuine signature; `Bounds.unforgeable`
    then needs a witness in `p`'s `sent`, which starts and stays empty.
    `deposit` and `tick` never touch `status`; `transfer` and `reclaim` on
    `c` need `c` already finalized, which it never is. Restated against the
    explicit-time game's `Threat.RoundSeq` (operator ruling 2026-10-29): the
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
  | land hsplit _ _ => rw [← hpnil] at hsplit; simp at hsplit
  | @tick pending net1 net2 dt hfeas hgate hrest ih =>
    intro hsent1 hbase1
    have hsent1' : (net1.applyAdv apps (AdvMove.tick dt)).sent = [] := by
      rw [NetworkState.applyAdv_sent]; exact hsent1
    have step : (net1.applyAdv apps (AdvMove.tick dt)).chain.statusOf c = .open t0 := by
      simpa [NetworkState.applyAdv] using hbase1
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
            have hs' : net1.chain.tick dt' = s' := by simpa using h
            subst hs'; rw [Adjudicator.tick_statusOf]; exact hbase1
          | transfer a b =>
            by_cases hac : a = c
            · subst hac
              obtain ⟨o, -, -, hfo, -, -, -, -, -, -, -, -⟩ := Adjudicator.transfer_some h
              rw [hfo1] at hfo; exact absurd hfo (by simp)
            · obtain ⟨_, _, _, _, _, _, _, _, hs, _, _, _⟩ := Adjudicator.transfer_some h
              rw [Adjudicator.statusOf_of_status hs, Adjudicator.statusOf_setStatus,
                if_neg (Ne.symm hac)]
              exact hbase1
          | reclaim l v =>
            by_cases hlc : l = c
            · subst hlc
              obtain ⟨oL, -, -, -, -, hfo, -, -, -, -, -, -, -, -⟩ := Adjudicator.reclaim_some h
              rw [hfo1] at hfo; exact absurd hfo (by simp)
            · obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hsr, _, _⟩ := Adjudicator.reclaim_some h
              rw [hsr, Adjudicator.statusOf_setStatus, if_neg (Ne.symm hlc)]
              exact hbase1
          | challenge c' proof candidate =>
            by_cases hcc : c' = c
            · exfalso; subst hcc
              obtain ⟨⟨-, hs, -, -⟩, -⟩ := Adjudicator.challenge_some h
              rw [hc] at hs
              match proof, hs with
              | [ss'], hs =>
                simp only [consensusRules, Bool.and_eq_true, decide_eq_true_eq] at hs
                obtain ⟨⟨-, hch⟩, hall⟩ := hs
                obtain ⟨x, hx, -⟩ := hU ss' (List.mem_singleton_self _) (hall p (hch ▸ hp))
                rw [hsent1] at hx; exact absurd hx List.not_mem_nil
            · obtain ⟨-, rfl⟩ := Adjudicator.challenge_some h
              rw [Adjudicator.statusOf_setStatus, if_neg (Ne.symm hcc)]
              exact hbase1
          | checkpoint c' proof candidate =>
            by_cases hcc : c' = c
            · exfalso; subst hcc
              obtain ⟨⟨-, hs, -, -⟩, -⟩ := Adjudicator.checkpoint_some h
              rw [hc] at hs
              match proof, hs with
              | [ss'], hs =>
                simp only [consensusRules, Bool.and_eq_true, decide_eq_true_eq] at hs
                obtain ⟨⟨-, hch⟩, hall⟩ := hs
                obtain ⟨x, hx, -⟩ := hU ss' (List.mem_singleton_self _) (hall p (hch ▸ hp))
                rw [hsent1] at hx; exact absurd hx List.not_mem_nil
            · obtain ⟨-, rfl⟩ := Adjudicator.checkpoint_some h
              rw [Adjudicator.statusOf_setStatus, if_neg (Ne.symm hcc)]
              exact hbase1
          | conclude c' ss' =>
            by_cases hcc : c' = c
            · exfalso; subst hcc
              obtain ⟨⟨-, hproof'⟩, -⟩ := Adjudicator.conclude_some h
              have hp' : p ∈ ss'.signers := hproof'.2.2 p (hproof'.1 ▸ hp)
              have hmem : ss' ∈ (Op.conclude c' ss').proofStates := by simp [Op.proofStates]
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
    (A : Assumptions apps p T) (net : NetworkState E p)
    (_hr : (Nitro.participant apps T).Reachable net)
    (hc : ∀ c : FixedPart, p ∈ c.participants → apps c.appDef = consensusRules)
    (hopen : ∀ c : FixedPart, p ∈ c.participants → ∃ t, net.chain.statusOf c = .open t)
    (hdag : net.chain.IsDAG) (hsent : net.sent = []) :
    Prevents apps T (fun net' => ∃ c : FixedPart, p ∈ c.participants ∧
      Relation.TransGen net'.chain.Edge c.address c.address) net := by
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
      refine ⟨by simpa [NetworkState.applyHonest] using hsent2, fun c' hpc' t ht => ?_⟩
      have hopen2 := consensus_channel_stays_open A.toBounds (hc c' hpc') hpc' hseq ihsent
        (ihopen c' hpc' t ht)
      simpa [NetworkState.applyHonest, Adjudicator.tick_statusOf] using hopen2
  refine ⟨fun _ => .wait 0, fun _ => trivial, fun n1 n2 hrun hround hcyc => ?_⟩
  obtain ⟨c, hpc, hcyc⟩ := hcyc
  obtain ⟨t, ht⟩ := hopen c hpc
  obtain ⟨hsent1, hopen1⟩ := hinv hrun
  obtain ⟨hseq, -⟩ := hround
  have hopenN2 : n2.chain.statusOf c = .open t :=
    consensus_channel_stays_open A.toBounds (hc c hpc) hpc hseq hsent1 (hopen1 c hpc t ht)
  obtain ⟨y, hey, -⟩ := Relation.TransGen.head'_iff.1 hcyc
  obtain ⟨-, e, he, -⟩ := hey
  simp [Adjudicator.allocationOf, hopenN2, ChannelStatus.finalOutcome_open] at he

/-- Nitro-33, Nitro-34, Nitro-32. Nitro:836-837: "it is impossible to find a strategy
    that gives any node a value higher than allocated by this algorithm."
    In the transfer-only game (Nitro:779-781), on a DAG of outcomes. -/
theorem turbo_value_upper_bound (apps : Apps E) {p : Participant} (T : Threat E p)
    (B : Bounds apps p T) (hT : T.TransfersOnly) (hcap : T.CapableTransfers)
    (net : NetworkState E p) (hr : (Nitro.participant apps T).Reachable net)
    (hdag : net.chain.IsDAG) (n : Address E) (v x : Coins)
    (hv : net.chain.TurboValue n v)
    (h : CanObtainIn apps T HonestMove.IsTransfer n x net) : x ≤ v := by
  sorry

/-- Nitro-33, Nitro-35, Nitro-18. Nitro:837-839: "It is also not hard to construct a
    strategy for a node to obtain the value allocated by the algorithm, if
    necessary by actually implementing the algorithm up until that node." In
    the transfer-only game, for an external destination. -/
theorem turbo_value_achievable (apps : Apps E) {p : Participant} (T : Threat E p)
    (B : Bounds apps p T) (hT : T.TransfersOnly) (hcap : T.CapableTransfers)
    (net : NetworkState E p) (hr : (Nitro.participant apps T).Reachable net)
    (hdag : net.chain.IsDAG) (d : E) (v : Coins)
    (hv : net.chain.TurboValue (.external d) v) :
    CanObtainIn apps T HonestMove.IsTransfer (.external d) v net := by
  sorry

/-- Nitro-18, Nitro-33, Nitro-34, Nitro-35. Nitro:482-484 with Nitro:835-839: on a Turbo DAG
    the value at `d` in the transfer-only game is the algorithm's value of
    `d`. -/
theorem turbo_value_is_value (apps : Apps E) {p : Participant} (T : Threat E p)
    (B : Bounds apps p T) (hT : T.TransfersOnly) (hcap : T.CapableTransfers)
    (net : NetworkState E p) (hr : (Nitro.participant apps T).Reachable net)
    (hdag : net.chain.IsDAG) (d : E) (v : Coins)
    (hv : net.chain.TurboValue (.external d) v) :
    ValueIn apps T HonestMove.IsTransfer d net v := by
  sorry

/-- Nitro-36. Nitro:842-843: "calling transfers out of order does not affect the
    ultimate result." Two exhausted transfer sequences from one Turbo state
    give the same balances. -/
theorem turbo_order_independent (apps : Apps E) (s : Adjudicator E) (hdag : s.IsDAG)
    (ops1 ops2 : List (Participant × Op E)) (h1 : OnlyTransfers ops1)
    (h2 : OnlyTransfers ops2) (hx1 : (Adjudicator.applyAll apps ops1 s).TransferExhausted)
    (hx2 : (Adjudicator.applyAll apps ops2 s).TransferExhausted) (a : Address E) :
    (Adjudicator.applyAll apps ops1 s).balances.get a =
      (Adjudicator.applyAll apps ops2 s).balances.get a := by
  sorry

/-- Nitro-33, Nitro-36, Nitro-32. Nitro:819 "Choose a topological ordering":
    on a DAG a topological ordering exists (Nitro:798-799) and the
    algorithm's value does not depend on which one is chosen, so
    `TurboValue` is a function. -/
theorem turbo_value_exists_unique (s : Adjudicator E) (hdag : s.IsDAG) (n : Address E) :
    (∃ v, s.TurboValue n v) ∧ ∀ v w, s.TurboValue n v → s.TurboValue n w → v = w := by
  sorry

/-- Nitro-37, Nitro-47, docs-0060-07, docs-0080-08. Nitro:859-865: "χ is funded with 6 coins by
    L for both A and B ... Once it is on-chain, the transfer operation
    T(L, χ, 6) is all that is required to make χ directly funded. From the
    Turbo redistribution result, we know that this redistribution strategy is
    unbeatable." G16 (`docs/nitro-repair-2026-10-27.md`, defect 23): the
    adversary can transfer `L → χ` and then `χ → q` within one prefix, so
    `χ` must not finalize during the strategy, as `ledger_partial_withdrawal`
    already requires of its receiving ledger. -/
theorem ledger_offload_funds_subchannel (apps : Apps E) (Ts : Threats E apps) (v : Views E)
    (n : Network E) (hr : (Nitro.network apps Ts).Reachable n)
    (hvn : v = n.views) (w : LedgerWithSub E) (hw : w.Holds apps Ts v)
    (hχopen : ∀ p, (v p).chain.finalOutcome w.χ.address = none)
    (hχsent : ∀ p, ∀ t ∈ (v p).sent, t.state.channel = w.χ → t.state.isFinal = false) :
    FundedFor apps (Ts.T w.A) w.χ w.c (v w.A) ∧ FundedFor apps (Ts.T w.B) w.χ w.c (v w.B) := by
  sorry

/-- Nitro-49 (Nitro:891-922, §5.4.1 Opening a Sub-channel), docs-0060-07. From
    `⟦L : x⟧, [L ↦ (A : a, B : b)]_{A,B}` and `[χ ↦ (A : a', B : b')]_{A,B}`
    with `a' ≤ a`, `b' ≤ b`, the update
    `[L ↦ (A : a − a', B : b − b', χ : a' + b')]_{A,B}` preserves the value
    of `A` and `B` at their destinations `dA` and `dB`. -/
theorem subchannel_open_value_preserving (apps : Apps E) (Ts : Threats E apps) (v v' : Views E)
    (n : Network E) (hr : (Nitro.network apps Ts).Reachable n)
    (hvn : v = n.views) (n' : Network E)
    (hr' : (Nitro.network apps Ts).Reachable n') (hvn' : v' = n'.views)
    (A B : Participant) (dA dB : E) (L χ : FixedPart)
    (a b a' b' : Coins) (ha : a' ≤ a) (hb : b' ≤ b)
    (hL : IsLedgerChannel apps L) (hLp : L.participants = [A, B]) (hχp : χ.participants = [A, B])
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

/-- Nitro-49 (Nitro:939-957, §5.4.2 Closing a Sub-channel), docs-0080-07. From
    `[L ↦ (A : a, B : b, χ : c)]_{A,B}` and the concluded
    `[χ ↦ (A : a', B : b')]_{A,B}` with `a' + b' = c`, the update
    `[L ↦ (A : a + a', B : b + b')]_{A,B}` preserves the value of `A` and
    `B`. -/
theorem subchannel_close_value_preserving (apps : Apps E) (Ts : Threats E apps) (v v' : Views E)
    (n : Network E) (hr : (Nitro.network apps Ts).Reachable n)
    (hvn : v = n.views) (n' : Network E)
    (hr' : (Nitro.network apps Ts).Reachable n') (hvn' : v' = n'.views)
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
    simp [Allocation.dedup, Allocation.dedupFrom, alloc, hAB, hAχ, Ne.symm hBχ]
  refine ⟨?_, ?_, ?_⟩
  · have := Allocation.paidTo_of_getElem? (held := a + b + c) hd (j := 2) (f := alloc A (a + a')) rfl
    refine this.trans ?_; simp [alloc, Allocation.total, Entry.amount]; grind
  · have := Allocation.paidTo_of_getElem? (held := a + b + c) hd (j := 0) (f := alloc B b) rfl
    refine this.trans ?_; simp [alloc, Allocation.total, Entry.amount]; grind
  · have := Allocation.paidTo_of_getElem? (held := a + b + c) hd (j := 1) (f := alloc χ c) rfl
    refine this.trans ?_; simp [alloc, Allocation.total, Entry.amount]; grind

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
      simp [Allocation.dedup, Allocation.dedupFrom, alloc, hAB, hAχ, Ne.symm hBχ]
    rw [hL]
    refine (Allocation.paidTo_of_getElem? hd1 (j := 2) (f := alloc A (a + a')) rfl).trans ?_
    simp [alloc, Allocation.total, Entry.amount]; grind
  · have hd2 : Allocation.dedup [alloc A (a + a'), alloc B b, alloc χ c] =
        [alloc A (a + a'), alloc B b, alloc χ c] := by
      simp [Allocation.dedup, Allocation.dedupFrom, alloc, Ne.symm hAB, Ne.symm hAχ, Ne.symm hBχ]
    rw [hL]
    refine (Allocation.paidTo_of_getElem? hd2 (j := 0) (f := alloc A (a + a')) rfl).trans ?_
    simp [alloc, Allocation.total, Entry.amount]; grind

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
    · rw [if_pos hca]; grind
    · rw [if_neg hca]
  | transfer a b =>
    by_cases hac : a = c
    · subst hac
      obtain ⟨o, amt, x, hf, -, -, -, -, -, -, -, -⟩ := Adjudicator.transfer_some h
      rw [hopen] at hf; simp at hf
    · obtain ⟨o, amt, x, hf, hfind, hxeq, hbal, -, hstat, hnow, hak, hbf⟩ := Adjudicator.transfer_some h
      have hca : (c.address : Address E) ≠ a.address := by
        intro hh; injection hh with hh'; exact hac hh'.symm
      rw [hbal, Balances.get_sub, if_neg hca, Balances.get_add]
      by_cases hbc : c.address = b
      · rw [if_pos hbc]; grind
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
    have hs' : s.tick dt = s' := by simpa using h
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
      · simpa [FixedPart.address_eq, Adjudicator.statusOf_of_status hs, hn] using hnone
      · rw [hb, Balances.get_add]
        by_cases hca : c.address = a
        · rw [if_pos hca]; grind
        · rw [if_neg hca]; exact hfund0
    | transfer a b =>
      by_cases hac : a = c
      · subst hac
        obtain ⟨oo, amtt, x, hf, -, -, -, -, -, -, -, -⟩ := Adjudicator.transfer_some h
        rw [hnone] at hf; simp at hf
      · left
        obtain ⟨oo, amtt, x, hf, hfind, hxeq, hbal, -, hstat, hnow, hak, hbf⟩ :=
          Adjudicator.transfer_some h
        have hca : (c.address : Address E) ≠ a.address := by
          intro hh; injection hh with hh'; exact hac hh'.symm
        refine ⟨?_, ?_⟩
        · simpa [FixedPart.address_eq, Adjudicator.statusOf_of_status hstat,
            Adjudicator.statusOf_setStatus, if_neg (Ne.symm hac), hnow] using hnone
        · rw [hbal, Balances.get_sub, if_neg hca, Balances.get_add]
          by_cases hbc : c.address = b
          · rw [if_pos hbc]; grind
          · rw [if_neg hbc]; exact hfund0
    | reclaim l v =>
      by_cases hcl : l = c
      · subst hcl
        obtain ⟨oL, -, -, -, -, hL, -, -, -, -, -, -, -, -⟩ := Adjudicator.reclaim_some h
        rw [hnone] at hL; simp at hL
      · left
        obtain ⟨oL, oV, x, left, right, hL, hV, hfind, hne1, hne2, hxeq, hsucc, hlk, hvk⟩ :=
          Adjudicator.reclaim_some h
        have hbal' : s'.balances = s.balances := by rw [hsucc]; rfl
        refine ⟨?_, ?_⟩
        · simpa [FixedPart.address_eq, hsucc, Adjudicator.statusOf_setStatus,
            if_neg (Ne.symm hcl)] using hnone
        · rw [hbal']; exact hfund0
    | challenge c' proof cand =>
      by_cases hcc : c' = c
      · subst hcc
        obtain ⟨-, hsucc⟩ := Adjudicator.challenge_some h
        have hbal' : s'.balances = s.balances := by rw [hsucc]; rfl
        by_cases hz : s.now + c'.challengeDuration ≤ s.now
        · right
          refine ⟨cand.outcome, ?_, ?_, ?_⟩
          · simp [hsucc, Adjudicator.finalizedWith_channel, FixedPart.address_eq,
              ChannelStatus.finalizedWith_challenged, hz]
          · simp [hsucc, Adjudicator.finalOutcome_channel, FixedPart.address_eq,
              ChannelStatus.finalOutcome_challenged, hz]
          · rw [hbal']; exact hfund0
        · left
          refine ⟨?_, ?_⟩
          · simp [hsucc, Adjudicator.finalOutcome_channel, FixedPart.address_eq,
              ChannelStatus.finalOutcome_challenged, hz]
          · rw [hbal']; exact hfund0
      · left
        obtain ⟨-, hsucc⟩ := Adjudicator.challenge_some h
        refine ⟨?_, ?_⟩
        · simpa [FixedPart.address_eq, hsucc, Adjudicator.statusOf_setStatus,
            if_neg (Ne.symm hcc)] using hnone
        · have hbal' : s'.balances = s.balances := by rw [hsucc]; rfl
          rw [hbal']; exact hfund0
    | checkpoint c' proof cand =>
      left
      by_cases hcc : c' = c
      · subst hcc
        obtain ⟨-, hsucc⟩ := Adjudicator.checkpoint_some h
        refine ⟨?_, ?_⟩
        · simp [hsucc, Adjudicator.finalOutcome_channel, FixedPart.address_eq]
        · have hbal' : s'.balances = s.balances := by rw [hsucc]; rfl
          rw [hbal']; exact hfund0
      · obtain ⟨-, hsucc⟩ := Adjudicator.checkpoint_some h
        refine ⟨?_, ?_⟩
        · simpa [FixedPart.address_eq, hsucc, Adjudicator.statusOf_setStatus,
            if_neg (Ne.symm hcc)] using hnone
        · have hbal' : s'.balances = s.balances := by rw [hsucc]; rfl
          rw [hbal']; exact hfund0
    | conclude c' ss' =>
      by_cases hcc : c' = c
      · subst hcc
        right
        obtain ⟨-, hsucc⟩ := Adjudicator.conclude_some h
        have hbal' : s'.balances = s.balances := by rw [hsucc]; rfl
        refine ⟨ss'.state.outcome, ?_, ?_, ?_⟩
        · simp [hsucc, Adjudicator.finalizedWith_channel, FixedPart.address_eq]
        · simp [hsucc, Adjudicator.finalOutcome_channel, FixedPart.address_eq]
        · rw [hbal']; exact hfund0
      · left
        obtain ⟨-, hsucc⟩ := Adjudicator.conclude_some h
        refine ⟨?_, ?_⟩
        · simpa [FixedPart.address_eq, hsucc, Adjudicator.statusOf_setStatus,
            if_neg (Ne.symm hcc)] using hnone
        · have hbal' : s'.balances = s.balances := by rw [hsucc]; rfl
          rw [hbal']; exact hfund0
    | tick dt =>
      have hs' : s.tick dt = s' := by simpa using h
      subst hs'
      rcases hstat : s.statusOf c with t' | ⟨t', ch⟩ | ⟨t', f, oo⟩
      · left
        refine ⟨?_, ?_⟩
        · simp [Adjudicator.finalOutcome_channel, FixedPart.address_eq,
            Adjudicator.tick_statusOf, hstat]
        · simpa using hfund0
      · by_cases hz : ch.deadline ≤ s.now + dt
        · right
          refine ⟨ch.state.outcome, ?_, ?_, ?_⟩
          · simp [Adjudicator.finalizedWith_channel, FixedPart.address_eq,
              Adjudicator.tick_statusOf, hstat, ChannelStatus.finalizedWith_challenged, hz]
          · simp [Adjudicator.finalOutcome_channel, FixedPart.address_eq,
              Adjudicator.tick_statusOf, hstat, ChannelStatus.finalOutcome_challenged, hz]
          · simpa using hfund0
        · left
          refine ⟨?_, ?_⟩
          · simp [Adjudicator.finalOutcome_channel, FixedPart.address_eq,
              Adjudicator.tick_statusOf, hstat, ChannelStatus.finalOutcome_challenged, hz]
          · simpa using hfund0
      · exfalso
        have hcontra : s.finalOutcome c.address = some oo := by
          simp [Adjudicator.finalOutcome_channel, FixedPart.address_eq, hstat]
        rw [hcontra] at hnone; simp at hnone

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
  | tick dt => simp at h; subst h; rfl
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
    (hbounds : Bounds apps p T) {c2 : FixedPart}
    (hc2app : apps c2.appDef = consensusRules) (hp2 : p ∈ c2.participants)
    (hdur2 : 2 * T.ε ≤ c2.challengeDuration) {D v0now : Time} (hD : D ≤ v0now + 2 * T.ε) :
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
      simpa [FixedPart.address_eq, Adjudicator.finalOutcome_channel] using hfo
    have hfl' : ∀ t0 ch, (net1.applyAdv apps (.land op)).chain.statusOf c2 = .challenged t0 ch →
        D ≤ ch.deadline := by rw [hstat]; exact hfl
    have hsent' : ∀ t0 ∈ (net1.applyAdv apps (.land op)).sent, t0.state.channel = c2 →
        t0.state.isFinal = false := by rw [NetworkState.applyAdv_sent]; exact hsent
    have hlo' : v0now ≤ (net1.applyAdv apps (.land op)).chain.now := by rw [hnow]; exact hlo
    exact ih hpend' hpnotick' hDbound hlo' hfo' hfl' hsent'
  | @tick pending net1 net2 dt hfeas hgate hrest ih =>
    intro hpend hpnotick hDbound hlo hfo hfl hsent
    have hstat : (net1.applyAdv apps (AdvMove.tick dt)).chain.statusOf c2 = net1.chain.statusOf c2 := by
      simp [NetworkState.applyAdv]
    have hadv : (net1.applyAdv apps (AdvMove.tick dt)).chain.now ≤ net2.chain.now := by
      simpa using hrest.now_le
    have hfo' : (net1.applyAdv apps (AdvMove.tick dt)).chain.finalOutcome c2.address = none := by
      have hfo0 : (net1.chain.statusOf c2).finalOutcome net1.chain.now = none := by
        simpa [FixedPart.address_eq, Adjudicator.finalOutcome_channel] using hfo
      simp only [FixedPart.address_eq, Adjudicator.finalOutcome_channel, hstat]
      rcases hst : net1.chain.statusOf c2 with s | ⟨t0, ch⟩ | ⟨t0, f, o⟩
      · simp [ChannelStatus.finalOutcome]
      · have hdl := hfl t0 ch hst
        have hlt : (net1.applyAdv apps (AdvMove.tick dt)).chain.now < ch.deadline :=
          lt_of_le_of_lt hadv (lt_of_lt_of_le hDbound hdl)
        simp only [ChannelStatus.finalOutcome, if_neg (not_le.mpr hlt)]
      · rw [hst] at hfo0; simp [ChannelStatus.finalOutcome] at hfo0
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
      | deliver _ => simpa [NetworkState.applyAdv] using And.intro hfo hfl
      | chain caller op =>
        simp only [NetworkState.applyAdv]
        cases h : net1.chain.apply apps caller op with
        | none => exact ⟨hfo, hfl⟩
        | some s' =>
          cases op with
          | deposit a e x =>
            have hop2 : ¬ Op.targets (Op.deposit a e x) c2 := by simp [Op.targets]
            have hntk : ∀ dt, Op.deposit a e x ≠ Op.tick dt := by intro dt heq; cases heq
            have hstat := statusOf_apply_of_not_targets h hop2
            have hn := Adjudicator.apply_now_eq_of_not_tick hntk h
            refine ⟨?_, by rw [hstat]; exact hfl⟩
            simp only [FixedPart.address_eq, Adjudicator.finalOutcome_channel, hstat, hn]
            simpa [FixedPart.address_eq, Adjudicator.finalOutcome_channel] using hfo
          | tick dt' =>
            have hstat : s'.statusOf c2 = net1.chain.statusOf c2 := by
              have hs' : net1.chain.tick dt' = s' := by simpa using h
              rw [← hs']; rfl
            have heq : (net1.applyAdv apps (AdvMove.chain caller (Op.tick dt'))).chain = s' := by
              simp [NetworkState.applyAdv, h]
            have hadv : s'.now ≤ net2.chain.now := by
              have := hrest.now_le; rw [heq] at this; exact this
            have hfo0 : (net1.chain.statusOf c2).finalOutcome net1.chain.now = none := by
              simpa [FixedPart.address_eq, Adjudicator.finalOutcome_channel] using hfo
            refine ⟨?_, by rw [hstat]; exact hfl⟩
            simp only [FixedPart.address_eq, Adjudicator.finalOutcome_channel, hstat]
            rcases hst : net1.chain.statusOf c2 with s | ⟨t0, ch⟩ | ⟨t0, f, o⟩
            · simp [ChannelStatus.finalOutcome]
            · have hdl := hfl t0 ch hst
              have hlt : s'.now < ch.deadline := lt_of_le_of_lt hadv (lt_of_lt_of_le hDbound hdl)
              simp only [ChannelStatus.finalOutcome, if_neg (not_le.mpr hlt)]
            · rw [hst] at hfo0; simp [ChannelStatus.finalOutcome] at hfo0
          | transfer a b =>
            by_cases hop2 : Op.targets (Op.transfer a b) c2
            · exfalso
              simp only [Op.targets] at hop2; subst hop2
              obtain ⟨o, -, -, hfo2, -, -, -, -, -, -, -, -⟩ := Adjudicator.transfer_some h
              rw [hfo] at hfo2; exact absurd hfo2 (by simp)
            · have hntk : ∀ dt, Op.transfer a b ≠ Op.tick dt := by intro dt heq; cases heq
              have hstat := statusOf_apply_of_not_targets h hop2
              have hn := Adjudicator.apply_now_eq_of_not_tick hntk h
              refine ⟨?_, by rw [hstat]; exact hfl⟩
              simp only [FixedPart.address_eq, Adjudicator.finalOutcome_channel, hstat, hn]
              simpa [FixedPart.address_eq, Adjudicator.finalOutcome_channel] using hfo
          | reclaim rl rv =>
            by_cases hop2 : Op.targets (Op.reclaim (E := E) rl rv) c2
            · exfalso
              simp only [Op.targets] at hop2; subst hop2
              obtain ⟨oL, -, -, -, -, hfo2, -, -, -, -, -, -, -, -⟩ := Adjudicator.reclaim_some h
              rw [hfo] at hfo2; exact absurd hfo2 (by simp)
            · have hntk : ∀ dt, Op.reclaim (E := E) rl rv ≠ Op.tick dt := by intro dt heq; cases heq
              have hstat := statusOf_apply_of_not_targets h hop2
              have hn := Adjudicator.apply_now_eq_of_not_tick hntk h
              refine ⟨?_, by rw [hstat]; exact hfl⟩
              simp only [FixedPart.address_eq, Adjudicator.finalOutcome_channel, hstat, hn]
              simpa [FixedPart.address_eq, Adjudicator.finalOutcome_channel] using hfo
          | challenge c' proof cand =>
            by_cases hop2 : Op.targets (Op.challenge c' proof cand) c2
            · simp only [Op.targets] at hop2; subst hop2
              obtain ⟨-, hsucc⟩ := Adjudicator.challenge_some h
              have hsnow : s'.now = net1.chain.now := by rw [hsucc]; rfl
              have hge : D ≤ net1.chain.now + c'.challengeDuration :=
                le_trans (le_trans hD (Nat.add_le_add_right hlo (2 * T.ε)))
                  (Nat.add_le_add_left hdur2 net1.chain.now)
              refine ⟨?_, ?_⟩
              · rw [FixedPart.address_eq, Adjudicator.finalOutcome_channel, hsnow, hsucc,
                  Adjudicator.statusOf_setStatus, if_pos rfl]
                have hself0 : T.ε ≤ 2 * T.ε := by rw [Nat.two_mul]; exact Nat.le_add_left T.ε T.ε
                have hpos : 0 < c'.challengeDuration := lt_of_lt_of_le T.ε_pos (le_trans hself0 hdur2)
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
              simpa [FixedPart.address_eq, Adjudicator.finalOutcome_channel] using hfo
          | checkpoint c' proof cand =>
            by_cases hop2 : Op.targets (Op.checkpoint c' proof cand) c2
            · simp only [Op.targets] at hop2; subst hop2
              obtain ⟨-, hsucc⟩ := Adjudicator.checkpoint_some h
              refine ⟨?_, ?_⟩
              · rw [FixedPart.address_eq, Adjudicator.finalOutcome_channel, hsucc,
                  Adjudicator.statusOf_setStatus, if_pos rfl]
                simp [ChannelStatus.finalOutcome]
              · intro t0 ch hc
                rw [hsucc, Adjudicator.statusOf_setStatus, if_pos rfl] at hc
                cases hc
            · have hntk : ∀ dt, Op.checkpoint c' proof cand ≠ Op.tick dt := by intro dt heq; cases heq
              have hstat := statusOf_apply_of_not_targets h hop2
              have hn := Adjudicator.apply_now_eq_of_not_tick hntk h
              refine ⟨?_, by rw [hstat]; exact hfl⟩
              simp only [FixedPart.address_eq, Adjudicator.finalOutcome_channel, hstat, hn]
              simpa [FixedPart.address_eq, Adjudicator.finalOutcome_channel] using hfo
          | conclude c' ss' =>
            by_cases hop2 : Op.targets (Op.conclude c' ss') c2
            · exfalso
              simp only [Op.targets] at hop2; subst hop2
              obtain ⟨⟨-, hproof'⟩, -⟩ := Adjudicator.conclude_some h
              have hp' : p ∈ ss'.signers := hproof'.2.2 p (hproof'.1 ▸ hp2)
              have hmem2 : ss' ∈ (Op.conclude c' ss').proofStates := by simp [Op.proofStates]
              obtain ⟨t', htmem, hteq⟩ :=
                (hbounds.unforgeable net1 caller (.conclude c' ss') hfeas ss' hmem2).1 hp'
              have hnf := hsent t' htmem (by rw [hteq]; exact hproof'.1)
              have hxfinal : t'.state.isFinal = true := by rw [hteq]; exact hproof'.2.1
              rw [hnf] at hxfinal; exact absurd hxfinal (by simp)
            · have hntk : ∀ dt, Op.conclude c' ss' ≠ Op.tick dt := by intro dt heq; cases heq
              have hstat := statusOf_apply_of_not_targets h hop2
              have hn := Adjudicator.apply_now_eq_of_not_tick hntk h
              refine ⟨?_, by rw [hstat]; exact hfl⟩
              simp only [FixedPart.address_eq, Adjudicator.finalOutcome_channel, hstat, hn]
              simpa [FixedPart.address_eq, Adjudicator.finalOutcome_channel] using hfo
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
    simpa [FixedPart.address_eq] using hf
  have hfin : (s.statusOf c).mode s.now = .finalized := by
    rw [ChannelStatus.mode_eq_finalized_iff, hf0]; rfl
  cases op with
  | deposit a e x =>
    obtain ⟨⟨c', hac', -⟩, -, hb, -, hs, hn⟩ := Adjudicator.deposit_some h
    refine ⟨o, amt, ?_, ?_, hd, ?_⟩
    · simpa [FixedPart.address_eq, Adjudicator.statusOf_of_status hs, hn] using hf
    · rw [hb, Balances.get_add]
      by_cases hca : c.address = a
      · rw [if_pos hca]; grind
      · rw [if_neg hca]; exact ht
    · rw [hb, Balances.get_add]
      by_cases hda : d.address = a
      · rw [if_pos hda]; grind
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
        simp [FixedPart.address_eq, hstatc]
      have hxb : x ≤ o.owed b := hxeq ▸ paidTo_first_entry_only _ _ _
      have htot := Allocation.total_reduceOwed o b hxb
      have hxh : x ≤ s.balances.get a.address := hxeq ▸ Allocation.paidTo_le_held _ _ _
      have hcd : (d.address : Address E) ≠ a.address := by
        intro hh; rw [hh, hf] at hdopen; simp at hdopen
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
          · rw [hba, Balances.get_add, if_pos rfl]; grind
          · rw [Balances.get_add, if_neg (Ne.symm hba)]; grind
        · rw [hbal, Balances.get_sub, if_neg hcd, Balances.get_add, if_pos rfl]
          grind
      · rw [if_neg hbd] at hfind'
        refine ⟨o.reduceOwed b x, amt, hfo', ?_, by rw [hfind']; exact hd, ?_⟩
        · rw [hbal, Balances.get_sub, if_pos rfl]
          by_cases hba : b = a.address
          · rw [hba, Balances.get_add, if_pos rfl]; grind
          · rw [Balances.get_add, if_neg (Ne.symm hba)]; grind
        · rw [hbal, Balances.get_sub, if_neg hcd, Balances.get_add, if_neg hbd]
    · obtain ⟨o'', amt'', x, hf'', hfind, hxeq, hbal, -, hstat, hnow, hak, hbf⟩ :=
        Adjudicator.transfer_some h
      have haddr : (c.address : Address E) ≠ a.address := by
        intro hh; injection hh with hh'; exact hac hh'.symm
      have hstatc : s'.statusOf c = s.statusOf c := by
        rw [Adjudicator.statusOf_of_status hstat, Adjudicator.statusOf_setStatus, if_neg (Ne.symm hac)]
      have hcd : (d.address : Address E) ≠ a.address := by
        intro hh; rw [hh, hf''] at hdopen; simp at hdopen
      refine ⟨o, amt, ?_, ?_, hd, ?_⟩
      · simpa [FixedPart.address_eq, hstatc, hnow] using hf
      · rw [hbal, Balances.get_sub, if_neg haddr, Balances.get_add]
        by_cases hbc : c.address = b
        · rw [if_pos hbc]; grind
        · rw [if_neg hbc]; exact ht
      · rw [hbal, Balances.get_sub, if_neg hcd, Balances.get_add]
        by_cases hbd : d.address = b
        · rw [if_pos hbd]; grind
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
        simp [FixedPart.address_eq, hstatl]
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
        simp at hiso
      have hfind1 : (o.addTo left (oV.amountAt 0)).find d.address =
          some ⟨d.address, .alloc (if d.address = left
            then amt + oV.amountAt 0 else amt)⟩ := by
        by_cases hld : d.address = left
        · rw [if_pos hld, ← hld, Allocation.find_addTo_self, hd]; simp
        · rw [if_neg hld, Allocation.find_addTo_of_ne _ _ hld, hd]
      have hfind2 : ((o.addTo left (oV.amountAt 0)).addTo right (oV.amountAt 1)).find
          d.address = some ⟨d.address, .alloc
            ((if d.address = left then amt + oV.amountAt 0 else amt) +
              (if d.address = right then oV.amountAt 1 else 0))⟩ := by
        by_cases hrd : d.address = right
        · rw [if_pos hrd, ← hrd, Allocation.find_addTo_self, hfind1]; simp
        · rw [if_neg hrd, Allocation.find_addTo_of_ne _ _ hrd, hfind1]; simp
      have hfind3 : (((o.addTo left (oV.amountAt 0)).addTo right (oV.amountAt 1)).remove
          v.address).find d.address = some ⟨d.address, .alloc
            ((if d.address = left then amt + oV.amountAt 0 else amt) +
              (if d.address = right then oV.amountAt 1 else 0))⟩ := by
        rw [Allocation.find_remove, if_neg had, hfind2]
      refine ⟨_, _, hfo', ?_, hfind3, ?_⟩
      · rw [hbal']; grind
      · rw [hbal']
        split <;> split <;> grind
    · obtain ⟨oL, oV, x, left, right, hL, hV, hfind, -, -, hxeq, hsucc, hlk, hvk⟩ :=
        Adjudicator.reclaim_some h
      have hstatc : s'.statusOf c = s.statusOf c := by
        rw [hsucc, Adjudicator.statusOf_setStatus, if_neg (Ne.symm hcl)]
      have hnow : s'.now = s.now := by rw [hsucc]; rfl
      have hbal' : s'.balances = s.balances := by rw [hsucc]; rfl
      refine ⟨o, amt, ?_, ?_, hd, ?_⟩
      · simpa [FixedPart.address_eq, hstatc, hnow] using hf
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
      · simpa [FixedPart.address_eq, hstatc, hnow] using hf
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
      · simpa [FixedPart.address_eq, hstatc, hnow] using hf
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
      · simpa [FixedPart.address_eq, hstatc, hnow] using hf
      · rw [hbal']; exact ht
      · rw [hbal']
  | tick dt =>
    have hs' : s.tick dt = s' := by simpa using h
    subst hs'
    refine ⟨o, amt, ?_, ?_, hd, ?_⟩
    · simpa [FixedPart.address_eq] using
        ChannelStatus.finalOutcome_mono hf0 (Nat.le_add_right s.now dt)
    · simpa using ht
    · simp

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
    simp [NetworkState.applyAdv, happly]
  have hmono := balance_mono_open_steps h2.steps hx
  rw [hchain, hbal, if_neg hxc] at hmono
  have hpaid : amt1 ≤ o1.paidTo (m.chain.balances.get c.address) x := by
    have hsub : o1.dedup.total ≤ o1.total :=
      Allocation.total_le_of_sublist (Allocation.dedupFrom_sublist [] o1)
    have hdedup_le : o1.dedup.total ≤ m.chain.balances.get c.address := le_trans hsub ht1
    have howed1 : o1.owed x = amt1 := by simp [Allocation.owed, hd1]
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
    (by simpa [HonestMove.Feasible_chain, Op.HonestFeasible, Op.proofStates] using hh) ?_
  intro n1 hround1
  obtain ⟨hseq1, hε1⟩ := hround1
  simp only [HonestMove.calls_chain] at hseq1
  simp only [NetworkState.applyHonest_chain]
  refine UnbeatableIn.move (.chain (.transfer c x)) trivial
    (by simp [HonestMove.Feasible_chain, Op.HonestFeasible, Op.proofStates]) ?_
  intro n2 hround2
  obtain ⟨hseq2, hε2⟩ := hround2
  simp only [HonestMove.calls_chain] at hseq2
  have hx2 := hxopen n1 n2 hseq1 hε1 hseq2 hε2
  have hx1 := finalOutcome_none_of_steps hseq2.steps hx2
  have hfin := conclude_round_finalized A.toBounds hp hdur hproof hΩ hseq1 hε1 hsent hopen hpend
  have hph : n1.chain.PayPhase c o x amt0 (net.chain.balances.get x) :=
    Adjudicator.PayPhase.steps hseq1.steps hd hx1
      (Or.inl ⟨finalOutcome_eq_none_iff.mpr hopen, htot, le_refl _⟩)
  apply UnbeatableIn.done
  simpa using transfer_round_pays hk hxf hxc hseq2 hx2 (hph.pays hfin)

/-- Nitro-49 (Nitro:997-1047, §5.4.4 Partial Withdrawal from a Ledger Channel).
    Nitro:1046-1047: "A was able to withdraw their funds instantly, without
    having to wait for the channel timeout." With the conclusion proof for
    `[L ↦ (L' : a + b + c, A : a')]_{A,B}` and `⟦L : x⟧`, `A` obtains `a'`
    at `dA` with no wait, and `L'` is funded with `a + b + c` for `A` and
    `B`. `L'` cannot finalize before `L` pays it: no running challenge of
    `L'` ends within `2 * ε`, no participant signed a final state of `L'`,
    and a challenge of `L'` lasts at least `2 * ε`.

    Operator ruling 2026-10-29: `v` is `n.views` for a reachable `Network`
    `n` (`Nitro.network`); a reachable chain never holds coins in `χ`, a
    virtual-kind channel (`Reachable.balances_virtual_zero`,
    `Nitro.network_chain_reachable`), which is the unreachable
    counterexample's shape. `v` and `hv` stay as they were: the shorter
    restatement adds `n`, `hr` and the link `hvn`, rather than rewriting
    every one of this theorem's existing uses of `v` to `n.views`. -/
theorem ledger_partial_withdrawal (apps : Apps E) (Ts : Threats E apps) (v : Views E)
    (n : Network E) (hr : (Nitro.network apps Ts).Reachable n)
    (hvn : v = n.views) (A B : Participant) (dA dB : E) (L L' χ : FixedPart) (a b c a' : Coins)
    (hL : IsLedgerChannel apps L) (hL' : IsLedgerChannel apps L') (hLp : L.participants = [A, B])
    (hL'p : L'.participants = [A, B]) (hLL' : L ≠ L')
    (hbal : v.HoldsBalance L.address (a + b + c + a'))
    (hconc : Concluded v L (.allocation [alloc L'.address (a + b + c), alloc (.external dA) a']))
    (hsent : ∀ p, ∀ t ∈ (v p).sent, t.state.channel = L → t.state.isFinal = true →
      t.state.outcome = .allocation [alloc L'.address (a + b + c), alloc (.external dA) a'])
    (hopen : ∀ p, (v p).chain.finalizedWith L.address = none)
    (hdur : ∀ p, 2 * (Ts.T p).ε ≤ L.challengeDuration ∧ 2 * (Ts.T p).ε ≤ L'.challengeDuration)
    (hpend : ∀ p, (v p).DeadlineAfter L (Ts.T p).ε ∧ (v p).DeadlineAfter L' (2 * (Ts.T p).ε))
    (hL'open : ∀ p, (v p).chain.finalOutcome L'.address = none)
    (hL'sent : ∀ p, ∀ t ∈ (v p).sent, t.state.channel = L' → t.state.isFinal = false)
    (hL'out : v.FinalizableBy apps Ts L'
      (.allocation [alloc (.external dA) a, alloc (.external dB) b, alloc χ.address c]) [A, B]) :
    UnbeatableNoWait apps (Ts.T A)
      (fun net' => (v A).chain.balances.get (.external dA) + a' ≤
        net'.chain.balances.get (.external dA))
      (v A) ∧
    FundedFor apps (Ts.T A) L' (a + b + c) (v A) ∧ FundedFor apps (Ts.T B) L' (a + b + c) (v B) := by
  obtain ⟨hLk, -⟩ := hL
  obtain ⟨hL'k, hL'app⟩ := hL'
  have hA : A ∈ L.participants := by simp [hLp]
  have hB : B ∈ L.participants := by simp [hLp]
  have hA' : A ∈ L'.participants := by simp [hL'p]
  have hB' : B ∈ L'.participants := by simp [hL'p]
  have htot : ∀ p, Allocation.total [alloc L'.address (a + b + c), alloc (.external dA) a'] ≤
      (v p).chain.balances.get L.address := by
    intro p
    rw [hbal p]
    simp [Allocation.total, alloc]
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
      obtain ⟨hfo1, hfl1, hs1⟩ := channel_stays_open_round (Ts.ok p).toBounds hL'app hp'
        (hdur p).2 (D := (v p).chain.now + 2 * (Ts.T p).ε) (v0now := (v p).chain.now) le_rfl
        hseq1 (by simpa [Op.targets] using hLL') (by simp) hb1 le_rfl (hL'open p)
        (hpend p).2 (hL'sent p)
      exact (channel_stays_open_round (Ts.ok p).toBounds hL'app hp' (hdur p).2
        (D := (v p).chain.now + 2 * (Ts.T p).ε) (v0now := (v p).chain.now) le_rfl hseq2
        (by simpa [Op.targets] using hLL') (by simp) hb2 hseq1.now_le hfo1 hfl1 hs1).1
    have hU := conclude_transfer_pays apps (Ts.T p) (Ts.ok p) (v p) hLk hp hh hproof hΩ
      (hsent p) (hopen p) (hdur p).1 (hpend p).1 (htot p) (x := L'.address) (amt0 := a + b + c)
      (by simp [Allocation.find, alloc]) (by simpa [Address.fundable] using hL'k)
      (by simpa [FixedPart.address_eq] using Ne.symm hLL') hxopen
    exact UnbeatableIn.mono (fun _ _ => trivial)
      (UnbeatableIn.imp (G2 := fun net' => net'.chain.DirectlyFundedWith L' (a + b + c))
        (fun h => le_trans (Nat.le_add_left _ _) h) hU)
  refine ⟨?_, hfund A hA hA', hfund B hB hB'⟩
  obtain ⟨ss, hh, hproof, hΩ⟩ := hconc A hA
  exact conclude_transfer_pays apps (Ts.T A) (Ts.ok A) (v A) hLk hA hh hproof hΩ (hsent A)
    (hopen A) (hdur A).1 (hpend A).1 (htot A) (x := .external dA) (amt0 := a')
    (by simp [Allocation.find, alloc]) rfl (by simp) (fun _ _ _ _ _ _ => rfl)

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
  | [], hcon => simp [consensusRules] at hcon
  | _ :: _ :: _, hcon => simp [consensusRules] at hcon

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
      exact ⟨s, by simp, rfl, hval.1⟩
    | [s, ch], hval =>
      simp only [validateOutcomeChange, Bool.and_eq_true, decide_eq_true_eq] at hval
      exact ⟨s, by simp, rfl, satp_validChallenge_start hval.1⟩
    | [s, ch, re], hval =>
      simp only [validateOutcomeChange, Bool.and_eq_true, decide_eq_true_eq] at hval
      exact ⟨s, by simp, rfl, satp_validResponse_start hval.1⟩
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
      simpa using heq
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
  | refl => unfold SatpOrigin; simp [Adjudicator.statusOf, Adjudicator.genesis]
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
    (s : Adjudicator E) (hs : ReachableSigned apps signed s) (Ω : Outcome E)
    (hfin : s.finalOutcome r.V.address = some Ω) :
    ∃ Ω0, Redistributed Ω0 Ω ∧
      (((s.statusOf r.V).turnNumRecord = 0 ∧
        Ω0 = originalOutcome (r.dest alice) (r.dest bob) r.a0 r.b0) ∨
       (∃ a b, PairOutcome (r.dest alice) (r.dest bob) Ω0 a b ∧ a + b = r.a0 + r.b0)) := by
  have horig := satpOrigin_reachableSigned hr hV halice hbob hsigned hs
  simp only [FixedPart.address_eq, Adjudicator.finalOutcome_channel] at hfin
  unfold SatpOrigin at horig
  revert hfin horig
  cases s.statusOf r.V with
  | «open» t => simp
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
    (hdur : 2 * T.ε ≤ r.V.challengeDuration) (net : NetworkState E p)
    (hnr : (Nitro.participant apps T).Reachable net) (s1 : SignedState E)
    (hh : net.Holds s1) (hall : s1.ByAll) (hchan : s1.state.channel = r.V)
    (hv1 : s1.state.turnNum = 1)
    (h1 : s1.state.outcome = originalOutcome (r.dest alice) (r.dest bob) r.a0 r.b0)
    (hsent : ∀ t ∈ net.sent, t.state.channel = r.V →
      (t.state.turnNum ≤ 1 ∧ t.state.outcome = originalOutcome (r.dest alice) (r.dest bob) r.a0 r.b0) ∨
      (∃ a b, PairOutcome (r.dest alice) (r.dest bob) t.state.outcome a b ∧ a + b = r.a0 + r.b0))
    (hst : ∃ t, net.chain.statusOf r.V = .open t ∧ t ≤ 1) :
    Unbeatable apps T (fun net' => ∃ Ω a b, net'.Finalized r.V Ω ∧
      PairOutcome (r.dest alice) (r.dest bob) Ω a b ∧ a + b = r.a0 + r.b0) net := by
  sorry

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
    rest. -/
theorem satp_theorem_3_2 (apps : Apps E) {P : Participant} (T : Threat E P)
    (A : Assumptions apps P T) (r : Route E) (alice bob : Participant) (hr : r.WellFormed apps)
    (hV : apps r.V.appDef = satpVirtualRules)
    (halice : r.peers.head? = some alice) (hbob : r.peers.getLast? = some bob)
    (i : Nat) (hi : 1 ≤ i) (hin : i + 1 < r.peers.length) (hP : r.peers[i]? = some P)
    (Pprev Pnext : Participant) (hprev : r.peers[i - 1]? = some Pprev)
    (hnext : r.peers[i + 1]? = some Pnext)
    (Lm Lp : FixedPart) (hLm : r.ledgers[i - 1]? = some Lm) (hLp : r.ledgers[i]? = some Lp)
    (hdur : 2 * T.ε ≤ Lm.challengeDuration ∧ 2 * T.ε ≤ Lp.challengeDuration ∧
      2 * T.ε ≤ r.V.challengeDuration)
    (om op : Allocation E) (balm balp : Coins)
    (hom : r.LedgerAfterRound2 om Pprev P P balm r.b0)
    (hop : r.LedgerAfterRound2 op P Pnext P balp r.a0)
    (net : NetworkState E P) (hnr : (Nitro.participant apps T).Reachable net)
    (hHm : HoldsLatestLedger net Lm om) (hHp : HoldsLatestLedger net Lp op)
    (hVs : HoldsVirtualSetup net r alice bob true)
    (hpend : net.DeadlineAfter Lm T.ε ∧ net.DeadlineAfter Lp T.ε ∧ net.DeadlineAfter r.V T.ε)
    (hchain : net.chain.finalizedWith Lm.address = none ∧
      net.chain.finalizedWith Lp.address = none ∧ net.chain.finalizedWith r.V.address = none) :
    Unbeatable apps T (IntermediaryRecovered r Lm Lp balm balp
      (net.chain.balances.get (.external (r.dest P)))) net := by
  sorry

omit [DecidableEq E] in
/-- A status that is not `.finalized` with a payout already applied has the
    same stored outcome as its outcome of finalization. -/
theorem ChannelStatus.finalOutcome_eq_finalizedWith (st : ChannelStatus E) (now : Time)
    (h : ∀ t f o, st = .finalized t f o → f = o) : st.finalOutcome now = st.finalizedWith now := by
  cases st with
  | «open» t => rfl
  | challenged t ch => rfl
  | finalized t f o => simp [h t f o rfl]

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
        have haddr : (Address.external d : Address E) ≠ L.address := by simp [FixedPart.address_eq]
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
      · have hdne : (Address.external d : Address E) ≠ v.address := by simp [FixedPart.address_eq]
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
    fix the operator ruling (`armada-laconic`
    labbook/2026-10-29-machine-types-for-approval.md, "Time bounds per
    pending action") names: the earlier per-move game forced two
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
    (Lm Lp : FixedPart) (hLm : r.ledgers[i - 1]? = some Lm) (hLp : r.ledgers[i]? = some Lp)
    (hdur : 2 * T.ε ≤ Lm.challengeDuration ∧ 2 * T.ε ≤ Lp.challengeDuration)
    (om op : Allocation E) (balm balp : Coins)
    (hom : r.LedgerBeforeRound2 om P balm) (hop : r.LedgerBeforeRound2 op P balp)
    (net : NetworkState E P) (hnr : (Nitro.participant apps T).Reachable net)
    (hHm : HoldsLatestLedger net Lm om) (hHp : HoldsLatestLedger net Lp op)
    (hpend : net.DeadlineAfter Lm T.ε ∧ net.DeadlineAfter Lp T.ε)
    (hchain : net.chain.finalizedWith Lm.address = none ∧
      net.chain.finalizedWith Lp.address = none) :
    Unbeatable apps T (IntermediaryRecovered r Lm Lp balm balp
      (net.chain.balances.get (.external (r.dest P)))) net := by
  -- The route facts: both ledgers run the consensus app, `P` is a participant
  -- of each, and the two ledgers are distinct (their left peers differ).
  obtain ⟨-, -, hnodup, -, hled, -, -, -⟩ := hr
  obtain ⟨Pm, Qm, hPm, hQm, hLmp, ⟨-, hcm⟩, -⟩ := hled (i - 1) Lm hLm
  obtain ⟨Pp, Qp, hPp, -, hLpp, ⟨-, hcp⟩, -⟩ := hled i Lp hLp
  rw [Nat.sub_add_cancel hi, hP, Option.some.injEq] at hQm
  rw [hP, Option.some.injEq] at hPp
  subst hQm hPp
  have hPLm : P ∈ Lm.participants := by rw [hLmp]; simp
  have hPLp : P ∈ Lp.participants := by rw [hLpp]; simp
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
  have hU := latest_state_finalizable_two apps T A net hnr Lm Lp ssm ssp hne hcm hcp hPLm hPLp
    hhm hhp hallm hallp hchm hchp (fun t ht hc => (hsentm t ht hc).1)
    (fun t ht hc => (hsentp t ht hc).1)
    (fun t ht hc hfin => by rw [(hsentm t ht hc).2] at hfin; cases hfin)
    (fun t ht hc hfin => by rw [(hsentp t ht hc).2] at hfin; cases hfin)
    hdur.1 hdur.2 hst1 hst2
  rw [houtm, houtp] at hU
  -- Every chain step keeps the credit invariant, from the start to the goal.
  have hI0 : LedgerPairInv Lm Lp om op r.V.address (r.dest P)
      (balm + balp + net.chain.balances.get (.external (r.dest P))) net.chain := by
    have hcm0 : ledgerCredit net.chain Lm om (.external (r.dest P)) = balm := by
      unfold ledgerCredit; rw [if_neg (by rw [hchain.1]; simp)]; exact hom.1
    have hcp0 : ledgerCredit net.chain Lp op (.external (r.dest P)) = balp := by
      unfold ledgerCredit; rw [if_neg (by rw [hchain.2]; simp)]; exact hop.1
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

/-- SATP-20 (SATP:500-501): "We omit the analogous statement that can be stated
    for the end-users Alice and Bob." The analogue for Alice (`P0`, ledger
    `L0`): if `V` finalizes with `{A : A(a), B : A(b)}` and `a + b = a0 + b0`
    (go-nitro `reclaim` needs it, MultiAssetHolder.sol:365), Alice can
    finalize `L0` with no guarantee for `V` and her entry raised by `a` from
    its Round 2 level, so she is owed her pre-protocol balance minus `a0`
    plus `a`. -/
theorem satp_end_user_recovers (apps : Apps E) {P : Participant} (T : Threat E P)
    (A : Assumptions apps P T) (r : Route E) (alice bob : Participant) (hr : r.WellFormed apps)
    (hV : apps r.V.appDef = satpVirtualRules)
    (halice : r.peers.head? = some alice) (hbob : r.peers.getLast? = some bob)
    (hPA : P = alice) (P1 : Participant) (hP1 : r.peers[1]? = some P1)
    (L0 : FixedPart) (hL0 : r.ledgers[0]? = some L0)
    (hdur : 2 * T.ε ≤ L0.challengeDuration ∧ 2 * T.ε ≤ r.V.challengeDuration)
    (o : Allocation E) (bal : Coins) (ho : r.LedgerAfterRound2 o P P1 P bal r.a0)
    (net : NetworkState E P) (hnr : (Nitro.participant apps T).Reachable net)
    (hH : HoldsLatestLedger net L0 o)
    (hVs : HoldsVirtualSetup net r alice bob true)
    (a b : Coins) (hab : a + b = r.a0 + r.b0)
    (hfin : net.chain.finalOutcome r.V.address =
      some (.allocation [alloc (.external (r.dest alice)) a, alloc (.external (r.dest bob)) b]))
    (hpend : net.DeadlineAfter L0 T.ε)
    (hchain : net.chain.finalizedWith L0.address = none) :
    Unbeatable apps T (EndUserRecovered r L0 bal a
      (net.chain.balances.get (.external (r.dest P)))) net := by
  sorry

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
  have hext : ∀ e : E, (Address.external e : Address E) ≠ r.V.address := by simp
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
  · simp [s1, hne]
  · simp; rfl
  · rw [Allocation.owed_remove_of_ne _ (hext _), Allocation.owed_addTo_self _ ?_,
      Allocation.owed_addTo_of_ne _ _ (by simpa [dP, dPp] using h1), hVb]
    rw [Allocation.find_addTo_of_ne _ _ (by simpa [dP, dPp] using h1)]; exact hem.2
  · rw [Allocation.owed_remove_of_ne _ (hext _), Allocation.owed_addTo_of_ne _ _
      (by simpa [dP, dPn] using h2), Allocation.owed_addTo_self _ hep.1, hVa]
  · rw [Allocation.find_remove, if_pos rfl]
  · rw [Allocation.find_remove, if_pos rfl]

end ArmadaLean.Nitro
