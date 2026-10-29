/-
  Nitro protocol theorems: unbeatable strategies, finalizability, value
  algorithms, ledger and virtual channel constructions, and the SATP
  protocol guarantees. Every proof is `sorry`, except the theorems that read
  no game definition. Each doc comment cites the source lines and the
  property ids of `docs/nitro-theorems.md`. The repair of 2026-10-27 (every
  changed type, with its reason) is `docs/nitro-repair-2026-10-27.md`.
-/
import ArmadaLean.Nitro.Safety

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

/-- Nitro-16, Nitro-21, ForceMove-B01, ForceMove-C03, docs-0070-05, docs-0080-06. Nitro:395-398: "where
    the channel L itself has enough coins in the adjudicator to cover the
    entire allocation ... A will receive all x coins allocated to them in ω."
    The strategy is one transfer. The entry of `d` is an allocation item:
    go-nitro refuses to transfer a guarantee (MultiAssetHolder.sol:169-170). -/
theorem directly_funded_pays (apps : Apps E) {p : Participant} (T : Threat E p)
    (A : Assumptions apps p T) (net : NetworkState E p) (c : FixedPart) (o : Allocation E) (d : E)
    (hf : net.chain.finalOutcome c.address = some (.allocation o))
    (hfund : net.chain.DirectlyFunded c) (amt : Coins)
    (hd : o.find (.external d) = some ⟨.external d, .alloc amt⟩) :
    UnbeatableNoWait apps T
      (fun net' => net.chain.balances.get (.external d) + o.owed (.external d) ≤
        net'.chain.balances.get (.external d)) net := by
  sorry

/-- Nitro-17, Nitro-21, Nitro-16. Nitro:480-481 and Nitro:590-593: a finalized allocation
    in a channel funded for `p` pays `d` its allocation. The channel is
    finalized already: a strategy to finalize and a strategy to fund do not
    compose, because the second one starts from `net`. -/
theorem finalizable_funded_pays (apps : Apps E) {p : Participant} (T : Threat E p)
    (A : Assumptions apps p T) (net : NetworkState E p) (c : FixedPart) (o : Allocation E) (d : E)
    (hf : net.chain.finalOutcome c.address = some (.allocation o))
    (hfund : FundedFor apps T c o.total net) (amt : Coins)
    (hd : o.find (.external d) = some ⟨.external d, .alloc amt⟩) :
    CanObtain apps T (.external d) (net.chain.balances.get (.external d) + o.owed (.external d))
      net := by
  sorry


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

/-- Over a feasible sequence of adversary moves, the chain's clock only
    advances (`NetworkState.applyAdv_now_le`, by induction). -/
theorem Threat.FeasibleSeq.now_le {apps : Apps E} {p : Participant} {T : Threat E p}
    {net net' : NetworkState E p} {advs : List (AdvMove E)}
    (h : T.FeasibleSeq apps net advs net') : net.chain.now ≤ net'.chain.now := by
  induction h with
  | nil => exact le_refl _
  | cons _ _ ih => exact le_trans (NetworkState.applyAdv_now_le _ _ _) ih

/-- Over a feasible sequence of adversary moves, `p`'s own sent list never
    changes: only `p`'s own honest moves touch it (`NetworkState.applyAdv_sent`,
    by induction). Used by `latest_state_finalizable` to carry `hlatest`/
    `hfinal` from the original network state to the state reached after `p`'s
    own challenge move. -/
theorem Threat.FeasibleSeq.sent_eq {apps : Apps E} {p : Participant} {T : Threat E p}
    {net net' : NetworkState E p} {advs : List (AdvMove E)}
    (h : T.FeasibleSeq apps net advs net') : net'.sent = net.sent := by
  induction h with
  | nil => rfl
  | cons _ _ ih => rw [ih, NetworkState.applyAdv_sent]

/-- Within one round, channel `c` stays either finalized with `Ω` or open
    at the round's eventual end `net'`, given it starts that way. Once
    finalized with `Ω` it stays so (`Adjudicator.finalizedWith_apply`). A
    fresh or renewed challenge on `c` cannot expire before `net'`: its
    deadline is set at least `c.challengeDuration ≥ 2 * T.ε` past the
    current clock (`hdur`), and the round itself ends strictly before
    `T.ε` has passed from that same clock (`hεbound`, per step).
    An adversary `conclude` on `c` still needs `p`'s genuine signature
    (`hbounds.unforgeable`, `hp`), which `p` only ever put on a final state
    of `c` that already carries `Ω` (`hsent`); so it cannot finalize `c`
    with anything but `Ω`. Used by `conclusion_proof_finalizable`. -/
theorem round_keeps_status {apps : Apps E} {p : Participant} {T : Threat E p}
    (hbounds : Bounds apps p T) {c : FixedPart} {Ω : Outcome E} (hp : p ∈ c.participants)
    (hdur : 2 * T.ε ≤ c.challengeDuration) :
    ∀ {net net' : NetworkState E p} {advs : List (AdvMove E)},
      T.FeasibleSeq apps net advs net' →
      net'.chain.now < net.chain.now + T.ε →
      (∀ t ∈ net.sent, t.state.channel = c → t.state.isFinal = true → t.state.outcome = Ω) →
      (net.chain.finalizedWith c.address = some Ω ∨ (net.chain.statusOf c).IsOpen net'.chain.now) →
      net'.chain.finalizedWith c.address = some Ω ∨ (net'.chain.statusOf c).IsOpen net'.chain.now := by
  intro net net' advs hseq
  induction hseq with
  | nil => intro _ _ hbase; exact hbase
  | @cons net1 net2 m rest hfeas hrest ih =>
    intro hεbound hsent hbase
    have step : net1.chain.finalizedWith c.address = some Ω ∨
        (net1.chain.statusOf c).IsOpen net2.chain.now →
        (net1.applyAdv apps m).chain.finalizedWith c.address = some Ω ∨
        ((net1.applyAdv apps m).chain.statusOf c).IsOpen net2.chain.now := by
      intro hbase1
      cases m with
      | deliver ss' => exact hbase1
      | tick dt =>
        rcases hbase1 with h | h
        · exact Or.inl (by
            simpa [NetworkState.applyAdv, FixedPart.address_eq] using
              ChannelStatus.finalizedWith_mono
                (by simpa [FixedPart.address_eq] using h) (Nat.le_add_right _ dt))
        · exact Or.inr (by simpa [NetworkState.applyAdv, Adjudicator.tick_statusOf] using h)
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
                obtain ⟨t, htmem, hteq⟩ := this
                have hΩ' := hsent t htmem (hteq ▸ hproof'.1) (hteq ▸ hproof'.2.1)
                simp [Adjudicator.finalizedWith_channel, hteq ▸ hΩ']
              · obtain ⟨-, rfl⟩ := Adjudicator.conclude_some h
                exact Or.inr (by
                  rw [Adjudicator.statusOf_setStatus, if_neg (Ne.symm hcc)]; exact hop)
    have hbase' := step hbase
    have hεbound' : net2.chain.now < (net1.applyAdv apps m).chain.now + T.ε :=
      lt_of_lt_of_le hεbound (Nat.add_le_add_right (NetworkState.applyAdv_now_le apps net1 m) T.ε)
    have hsent' : ∀ t ∈ (net1.applyAdv apps m).sent, t.state.channel = c →
        t.state.isFinal = true → t.state.outcome = Ω := by
      rw [NetworkState.applyAdv_sent]; exact hsent
    exact ih hεbound' hsent' hbase'

/-- Nitro-13, Nitro-21, Nitro-23, docs-0070-05, ForceMove-A14. SATP:286-289: a
    final state supported by all finalizes "without delay"; Nitro:296-299: a
    participant who holds a conclusion proof can register it; go-nitro
    `_conclude` accepts it from any caller. Under the consensus app no other
    participant can finalize a different outcome without `p`'s signature
    before `p`'s conclude lands, because a challenge lasts at least `2 * ε`
    and no running challenge ends within `ε` (Nitro:537-539). -/
theorem conclusion_proof_finalizable (apps : Apps E) {p : Participant} (T : Threat E p)
    (A : Assumptions apps p T) (net : NetworkState E p) (c : FixedPart) (ss : SignedState E)
    (Ω : Outcome E) (hc : apps c.appDef = consensusRules) (hp : p ∈ c.participants)
    (hh : net.Holds ss) (hproof : ConclusionProof c ss) (hΩ : ss.state.outcome = Ω)
    (hsent : ∀ t ∈ net.sent, t.state.channel = c → t.state.isFinal = true → t.state.outcome = Ω)
    (hchain : net.chain.finalizedWith c.address = none ∨ net.Finalized c Ω)
    (hdur : 2 * T.ε ≤ c.challengeDuration) (hpend : net.DeadlineAfter c T.ε) :
    UnbeatableNoWait apps T (fun net' => net'.Finalized c Ω) net := by
  rcases hchain with h1 | h2
  · refine UnbeatableIn.move (.chain (.conclude c ss)) trivial ?_ ?_
    · intro ss' hmem
      simp only [Op.proofStates, List.mem_singleton] at hmem
      subst hmem
      exact hh
    · intro advs net' hround
      obtain ⟨hseq, hεbound⟩ := hround
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
          rw [h1] at hfw
          exact absurd hfw (by simp)
      have hfinal := round_keeps_status A.toBounds hp hdur hseq hεbound hsent hbase
      rcases hfinal with hΩ' | hopen'
      · apply UnbeatableIn.done
        show (net'.applyHonest apps (.chain (.conclude c ss))).Finalized c Ω
        cases hcc : net'.chain.apply apps p (.conclude c ss) with
        | none =>
          simp only [NetworkState.Finalized, NetworkState.applyHonest, hcc, Option.getD_none]
          simpa [FixedPart.address_eq, Adjudicator.finalizedWith_channel] using hΩ'
        | some s' =>
          simp only [NetworkState.Finalized, NetworkState.applyHonest, hcc, Option.getD_some]
          simpa [FixedPart.address_eq, Adjudicator.finalizedWith_channel] using
            Adjudicator.finalizedWith_apply hcc hΩ'
      · apply UnbeatableIn.done
        show (net'.applyHonest apps (.chain (.conclude c ss))).Finalized c Ω
        have hsucc : net'.chain.conclude c ss =
            some (net'.chain.setStatus c (.finalized ss.state.turnNum ss.state.outcome ss.state.outcome)) := by
          unfold Adjudicator.conclude
          rw [if_pos (And.intro hopen' hproof)]
        simp only [NetworkState.Finalized, NetworkState.applyHonest, Adjudicator.apply_conclude,
          hsucc, Option.getD_some]
        simpa [FixedPart.address_eq, Adjudicator.finalizedWith_channel,
          Adjudicator.statusOf_setStatus, ChannelStatus.finalizedWith_finalized] using hΩ
  · exact UnbeatableIn.done h2

/-- One round of adversary play keeps the three-way disjunction that
    `latest_state_finalizable` reads at `net` compatible with the same
    disjunction read at `net'`, with `net'`'s own clock as the deadline
    bound. The turn number of any candidate the adversary submits for `c`
    is bounded by `ss.state.turnNum`: a candidate needs `p`'s genuine
    signature (`hbounds.unforgeable`), and `p` has sent nothing of `c`
    above `ss.state.turnNum` except `ss.state` itself (`hlatest`). A
    successful `conclude` therefore needs `p`'s signature on a final state
    of `c`, which `hfinal` ties to `ss.state.outcome`. A successful fresh
    `challenge`/`checkpoint` lands at a turn at or below `ss.state.turnNum`
    for the same reason, and a fresh challenge's deadline clears a full
    round (`hdur`, `2 * T.ε ≤ c.challengeDuration`). Used by
    `latest_state_finalizable`. -/
theorem latest_round_keeps_status {apps : Apps E} {p : Participant} {T : Threat E p}
    (hbounds : Bounds apps p T) {c : FixedPart} {ss : SignedState E}
    (hc : apps c.appDef = consensusRules) (hp : p ∈ c.participants)
    (hdur : 2 * T.ε ≤ c.challengeDuration) :
    ∀ {net net' : NetworkState E p} {advs : List (AdvMove E)},
      T.FeasibleSeq apps net advs net' →
      net'.chain.now < net.chain.now + T.ε →
      (∀ t ∈ net.sent, t.state.channel = c →
        t.state.turnNum < ss.state.turnNum ∨ t.state = ss.state) →
      (∀ t ∈ net.sent, t.state.channel = c → t.state.isFinal = true →
        t.state.outcome = ss.state.outcome) →
      (net.chain.finalizedWith c.address = some ss.state.outcome ∨
        (∃ t, net.chain.statusOf c = .open t ∧ t ≤ ss.state.turnNum) ∨
        (∃ t ch, net.chain.statusOf c = .challenged t ch ∧
          (t < ss.state.turnNum ∨ ch.state = ss.state) ∧ net'.chain.now < ch.deadline)) →
      net'.chain.finalizedWith c.address = some ss.state.outcome ∨
        (∃ t, net'.chain.statusOf c = .open t ∧ t ≤ ss.state.turnNum) ∨
        (∃ t ch, net'.chain.statusOf c = .challenged t ch ∧
          (t < ss.state.turnNum ∨ ch.state = ss.state) ∧ net'.chain.now < ch.deadline) := by
  intro net net' advs hseq
  induction hseq with
  | nil => intro _ _ _ hbase; exact hbase
  | @cons net1 net2 m rest hfeas hrest ih =>
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
        (∃ t, net1.chain.statusOf c = .open t ∧ t ≤ ss.state.turnNum) ∨
        (∃ t ch, net1.chain.statusOf c = .challenged t ch ∧
          (t < ss.state.turnNum ∨ ch.state = ss.state) ∧ net2.chain.now < ch.deadline)) →
        ((net1.applyAdv apps m).chain.finalizedWith c.address = some ss.state.outcome ∨
        (∃ t, (net1.applyAdv apps m).chain.statusOf c = .open t ∧ t ≤ ss.state.turnNum) ∨
        (∃ t ch, (net1.applyAdv apps m).chain.statusOf c = .challenged t ch ∧
          (t < ss.state.turnNum ∨ ch.state = ss.state) ∧ net2.chain.now < ch.deadline)) := by
      intro hbase1
      rcases hbase1 with hf | ⟨t, ho, hle⟩ | ⟨t, ch, hst, hdis, hdd⟩
      · refine Or.inl ?_
        cases m with
        | deliver _ => exact hf
        | tick dt =>
          simpa [NetworkState.applyAdv, FixedPart.address_eq] using
            ChannelStatus.finalizedWith_mono (by simpa [FixedPart.address_eq] using hf)
              (Nat.le_add_right _ dt)
        | chain caller op =>
          simp only [NetworkState.applyAdv]
          cases h : net1.chain.apply apps caller op with
          | none => simpa using hf
          | some s' => exact Adjudicator.finalizedWith_apply h hf
      · cases m with
        | deliver _ => exact Or.inr (Or.inl ⟨t, ho, hle⟩)
        | tick dt => exact Or.inr (Or.inl ⟨t, by simpa [NetworkState.applyAdv] using ho, hle⟩)
        | chain caller op =>
          simp only [NetworkState.applyAdv]
          cases h : net1.chain.apply apps caller op with
          | none => exact Or.inr (Or.inl ⟨t, ho, hle⟩)
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
              refine Or.inr (Or.inl ⟨t, ?_, hle⟩)
              rw [Adjudicator.statusOf_of_status hs]; exact ho
            | tick dt =>
              have hs' : net1.chain.tick dt = s' := by simpa using h
              subst hs'
              refine Or.inr (Or.inl ⟨t, ?_, hle⟩)
              rw [Adjudicator.tick_statusOf]; exact ho
            | transfer a b =>
              by_cases hac : a = c
              · subst hac
                obtain ⟨o, -, -, hfo, -, -, -, -, -, -, -, -⟩ := Adjudicator.transfer_some h
                rw [hfo1] at hfo; exact absurd hfo (by simp)
              · obtain ⟨_, _, _, _, _, _, _, _, hs, _, _, _⟩ := Adjudicator.transfer_some h
                refine Or.inr (Or.inl ⟨t, ?_, hle⟩)
                rw [Adjudicator.statusOf_of_status hs, Adjudicator.statusOf_setStatus,
                  if_neg (Ne.symm hac)]
                exact ho
            | reclaim l v =>
              by_cases hlc : l = c
              · subst hlc
                obtain ⟨oL, -, -, -, -, hfo, -, -, -, -, -, -, -, -⟩ := Adjudicator.reclaim_some h
                rw [hfo1] at hfo; exact absurd hfo (by simp)
              · obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hsr, _, _⟩ := Adjudicator.reclaim_some h
                refine Or.inr (Or.inl ⟨t, ?_, hle⟩)
                rw [hsr, Adjudicator.statusOf_setStatus, if_neg (Ne.symm hlc)]
                exact ho
            | challenge c' proof cand =>
              by_cases hcc : c' = c
              · subst hcc
                obtain ⟨⟨-, hs, -, -⟩, rfl⟩ := Adjudicator.challenge_some h
                rcases hsupp proof cand hU hs with hlt | heq
                · refine Or.inr (Or.inr ⟨cand.turnNum,
                    Challenge.mk cand (net1.chain.now + c'.challengeDuration), ?_, Or.inl hlt, ?_⟩)
                  · rw [Adjudicator.statusOf_setStatus, if_pos rfl]
                  · have hself : T.ε ≤ 2 * T.ε := by rw [Nat.two_mul]; exact Nat.le_add_left T.ε T.ε
                    have hge : T.ε ≤ c'.challengeDuration := le_trans hself hdur
                    exact lt_of_lt_of_le hεbound (Nat.add_le_add_left hge net1.chain.now)
                · refine Or.inr (Or.inr ⟨cand.turnNum,
                    Challenge.mk cand (net1.chain.now + c'.challengeDuration), ?_, Or.inr heq, ?_⟩)
                  · rw [Adjudicator.statusOf_setStatus, if_pos rfl]
                  · have hself : T.ε ≤ 2 * T.ε := by rw [Nat.two_mul]; exact Nat.le_add_left T.ε T.ε
                    have hge : T.ε ≤ c'.challengeDuration := le_trans hself hdur
                    exact lt_of_lt_of_le hεbound (Nat.add_le_add_left hge net1.chain.now)
              · obtain ⟨-, rfl⟩ := Adjudicator.challenge_some h
                refine Or.inr (Or.inl ⟨t, ?_, hle⟩)
                rw [Adjudicator.statusOf_setStatus, if_neg (Ne.symm hcc)]
                exact ho
            | checkpoint c' proof cand =>
              by_cases hcc : c' = c
              · subst hcc
                obtain ⟨⟨-, hs, -, -⟩, rfl⟩ := Adjudicator.checkpoint_some h
                refine Or.inr (Or.inl ⟨cand.turnNum, ?_, ?_⟩)
                · rw [Adjudicator.statusOf_setStatus, if_pos rfl]
                · rcases hsupp proof cand hU hs with hlt | heq
                  · exact le_of_lt hlt
                  · exact le_of_eq (by rw [heq])
              · obtain ⟨-, rfl⟩ := Adjudicator.checkpoint_some h
                refine Or.inr (Or.inl ⟨t, ?_, hle⟩)
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
                refine Or.inr (Or.inl ⟨t, ?_, hle⟩)
                rw [Adjudicator.statusOf_setStatus, if_neg (Ne.symm hcc)]
                exact ho
      · have hmono : net1.chain.now ≤ net2.chain.now :=
          le_trans (NetworkState.applyAdv_now_le apps net1 m) hrest.now_le
        have hltdl : net1.chain.now < ch.deadline := lt_of_le_of_lt hmono hdd
        cases m with
        | deliver _ => exact Or.inr (Or.inr ⟨t, ch, hst, hdis, hdd⟩)
        | tick dt =>
          refine Or.inr (Or.inr ⟨t, ch, ?_, hdis, hdd⟩)
          simpa [NetworkState.applyAdv] using hst
        | chain caller op =>
          simp only [NetworkState.applyAdv]
          cases h : net1.chain.apply apps caller op with
          | none => exact Or.inr (Or.inr ⟨t, ch, hst, hdis, hdd⟩)
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
              refine Or.inr (Or.inr ⟨t, ch, ?_, hdis, hdd⟩)
              rw [Adjudicator.statusOf_of_status hs]; exact hst
            | tick dt =>
              have hs' : net1.chain.tick dt = s' := by simpa using h
              subst hs'
              refine Or.inr (Or.inr ⟨t, ch, ?_, hdis, hdd⟩)
              rw [Adjudicator.tick_statusOf]; exact hst
            | transfer a b =>
              by_cases hac : a = c
              · subst hac
                obtain ⟨o, -, -, hfo, -, -, -, -, -, -, -, -⟩ := Adjudicator.transfer_some h
                rw [hfo1] at hfo; exact absurd hfo (by simp)
              · obtain ⟨_, _, _, _, _, _, _, _, hs, _, _, _⟩ := Adjudicator.transfer_some h
                refine Or.inr (Or.inr ⟨t, ch, ?_, hdis, hdd⟩)
                rw [Adjudicator.statusOf_of_status hs, Adjudicator.statusOf_setStatus,
                  if_neg (Ne.symm hac)]
                exact hst
            | reclaim l v =>
              by_cases hlc : l = c
              · subst hlc
                obtain ⟨oL, -, -, -, -, hfo, -, -, -, -, -, -, -, -⟩ := Adjudicator.reclaim_some h
                rw [hfo1] at hfo; exact absurd hfo (by simp)
              · obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hsr, _, _⟩ := Adjudicator.reclaim_some h
                refine Or.inr (Or.inr ⟨t, ch, ?_, hdis, hdd⟩)
                rw [hsr, Adjudicator.statusOf_setStatus, if_neg (Ne.symm hlc)]
                exact hst
            | challenge c' proof cand =>
              by_cases hcc : c' = c
              · subst hcc
                obtain ⟨⟨-, hs, -, -⟩, rfl⟩ := Adjudicator.challenge_some h
                rcases hsupp proof cand hU hs with hlt | heq
                · refine Or.inr (Or.inr ⟨cand.turnNum,
                    Challenge.mk cand (net1.chain.now + c'.challengeDuration), ?_, Or.inl hlt, ?_⟩)
                  · rw [Adjudicator.statusOf_setStatus, if_pos rfl]
                  · have hself : T.ε ≤ 2 * T.ε := by rw [Nat.two_mul]; exact Nat.le_add_left T.ε T.ε
                    have hge : T.ε ≤ c'.challengeDuration := le_trans hself hdur
                    exact lt_of_lt_of_le hεbound (Nat.add_le_add_left hge net1.chain.now)
                · refine Or.inr (Or.inr ⟨cand.turnNum,
                    Challenge.mk cand (net1.chain.now + c'.challengeDuration), ?_, Or.inr heq, ?_⟩)
                  · rw [Adjudicator.statusOf_setStatus, if_pos rfl]
                  · have hself : T.ε ≤ 2 * T.ε := by rw [Nat.two_mul]; exact Nat.le_add_left T.ε T.ε
                    have hge : T.ε ≤ c'.challengeDuration := le_trans hself hdur
                    exact lt_of_lt_of_le hεbound (Nat.add_le_add_left hge net1.chain.now)
              · obtain ⟨-, rfl⟩ := Adjudicator.challenge_some h
                refine Or.inr (Or.inr ⟨t, ch, ?_, hdis, hdd⟩)
                rw [Adjudicator.statusOf_setStatus, if_neg (Ne.symm hcc)]
                exact hst
            | checkpoint c' proof cand =>
              by_cases hcc : c' = c
              · subst hcc
                obtain ⟨⟨-, hs, -, -⟩, rfl⟩ := Adjudicator.checkpoint_some h
                refine Or.inr (Or.inl ⟨cand.turnNum, ?_, ?_⟩)
                · rw [Adjudicator.statusOf_setStatus, if_pos rfl]
                · rcases hsupp proof cand hU hs with hlt | heq
                  · exact le_of_lt hlt
                  · exact le_of_eq (by rw [heq])
              · obtain ⟨-, rfl⟩ := Adjudicator.checkpoint_some h
                refine Or.inr (Or.inr ⟨t, ch, ?_, hdis, hdd⟩)
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
                refine Or.inr (Or.inr ⟨t, ch, ?_, hdis, hdd⟩)
                rw [Adjudicator.statusOf_setStatus, if_neg (Ne.symm hcc)]
                exact hst
    have hbase' := step hbase
    have hεbound' : net2.chain.now < (net1.applyAdv apps m).chain.now + T.ε :=
      lt_of_lt_of_le hεbound (Nat.add_le_add_right (NetworkState.applyAdv_now_le apps net1 m) T.ε)
    have hlatest' : ∀ t ∈ (net1.applyAdv apps m).sent, t.state.channel = c →
        t.state.turnNum < ss.state.turnNum ∨ t.state = ss.state := by
      rw [NetworkState.applyAdv_sent]; exact hlatest
    have hfinal' : ∀ t ∈ (net1.applyAdv apps m).sent, t.state.channel = c →
        t.state.isFinal = true → t.state.outcome = ss.state.outcome := by
      rw [NetworkState.applyAdv_sent]; exact hfinal
    exact ih hεbound' hlatest' hfinal' hbase'

/-- One round of adversary play keeps "finalized with `ss.state.outcome`, or
    still challenged with the fixed `ch`" (`ch.state = ss.state`): the same
    turn-bound argument as `latest_round_keeps_status`, specialized to a
    status already at `ss.state.turnNum`, so no legal `challenge` or
    `checkpoint` can move it (a candidate's turn is at most
    `ss.state.turnNum`, by `hlatest`, but both operations need a turn
    strictly above the current record). Used by `latest_state_finalizable`
    for the wait phase, after `p`'s own challenge lands. -/
theorem latest_wait_keeps_status {apps : Apps E} {p : Participant} {T : Threat E p}
    (hbounds : Bounds apps p T) {c : FixedPart} {ss : SignedState E} {T0 : Nat} {ch : Challenge E}
    (hc : apps c.appDef = consensusRules) (hp : p ∈ c.participants) (hchs : ch.state = ss.state)
    (hT0 : ss.state.turnNum ≤ T0) :
    ∀ {net net' : NetworkState E p} {advs : List (AdvMove E)},
      T.FeasibleSeq apps net advs net' →
      (∀ t ∈ net.sent, t.state.channel = c →
        t.state.turnNum < ss.state.turnNum ∨ t.state = ss.state) →
      (∀ t ∈ net.sent, t.state.channel = c → t.state.isFinal = true →
        t.state.outcome = ss.state.outcome) →
      (net.chain.finalizedWith c.address = some ss.state.outcome ∨
        net.chain.statusOf c = .challenged T0 ch) →
      net'.chain.finalizedWith c.address = some ss.state.outcome ∨
        net'.chain.statusOf c = .challenged T0 ch := by
  intro net net' advs hseq
  induction hseq with
  | nil => intro _ _ hbase; exact hbase
  | @cons net1 net2 m rest hfeas hrest ih =>
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
        rcases hb with hlt | heq
        · exact le_of_lt hlt
        · exact le_of_eq (by rw [heq])
    have step : (net1.chain.finalizedWith c.address = some ss.state.outcome ∨
        net1.chain.statusOf c = .challenged T0 ch) →
        ((net1.applyAdv apps m).chain.finalizedWith c.address = some ss.state.outcome ∨
        (net1.applyAdv apps m).chain.statusOf c = .challenged T0 ch) := by
      intro hbase1
      rcases hbase1 with hf | hst
      · refine Or.inl ?_
        cases m with
        | deliver _ => exact hf
        | tick dt =>
          simpa [NetworkState.applyAdv, FixedPart.address_eq] using
            ChannelStatus.finalizedWith_mono (by simpa [FixedPart.address_eq] using hf)
              (Nat.le_add_right _ dt)
        | chain caller op =>
          simp only [NetworkState.applyAdv]
          cases h : net1.chain.apply apps caller op with
          | none => simpa using hf
          | some s' => exact Adjudicator.finalizedWith_apply h hf
      · by_cases hexp : ch.deadline ≤ net1.chain.now
        · have hf : net1.chain.finalizedWith c.address = some ss.state.outcome := by
            simp only [FixedPart.address_eq, Adjudicator.finalizedWith_channel, hst,
              ChannelStatus.finalizedWith_challenged, if_pos hexp, hchs]
          refine Or.inl ?_
          cases m with
          | deliver _ => exact hf
          | tick dt =>
            simpa [NetworkState.applyAdv, FixedPart.address_eq] using
              ChannelStatus.finalizedWith_mono (by simpa [FixedPart.address_eq] using hf)
                (Nat.le_add_right _ dt)
          | chain caller op =>
            simp only [NetworkState.applyAdv]
            cases h : net1.chain.apply apps caller op with
            | none => simpa using hf
            | some s' => exact Adjudicator.finalizedWith_apply h hf
        · cases m with
          | deliver _ => exact Or.inr hst
          | tick dt => exact Or.inr (by simpa [NetworkState.applyAdv] using hst)
          | chain caller op =>
            simp only [NetworkState.applyAdv]
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
    have hlatest' : ∀ t ∈ (net1.applyAdv apps m).sent, t.state.channel = c →
        t.state.turnNum < ss.state.turnNum ∨ t.state = ss.state := by
      rw [NetworkState.applyAdv_sent]; exact hlatest
    have hfinal' : ∀ t ∈ (net1.applyAdv apps m).sent, t.state.channel = c →
        t.state.isFinal = true → t.state.outcome = ss.state.outcome := by
      rw [NetworkState.applyAdv_sent]; exact hfinal
    exact ih hlatest' hfinal' hbase'

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
    (A : Assumptions apps p T) (net : NetworkState E p) (c : FixedPart) (ss : SignedState E)
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
    intro advs2 net3 hround2
    obtain ⟨hseq2, -⟩ := hround2
    have hmono2 : net2.chain.now ≤ net3.chain.now := hseq2.now_le
    have hlatest2 : ∀ t ∈ net2.sent, t.state.channel = c →
        t.state.turnNum < ss.state.turnNum ∨ t.state = ss.state := by rw [hsent2]; exact hlatest
    have hfinal2 : ∀ t ∈ net2.sent, t.state.channel = c → t.state.isFinal = true →
        t.state.outcome = ss.state.outcome := by rw [hsent2]; exact hfinal
    have hinv2 := latest_wait_keeps_status A.toBounds hc hp hch2s hT0 hseq2 hlatest2 hfinal2
      (Or.inr hch2)
    apply UnbeatableIn.done
    show (net3.applyHonest apps (.wait (ch2.deadline - net2.chain.now))).Finalized c
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
    (by simpa [HonestMove.Feasible, Op.proofStates] using hh) ?_
  intro advs net1 hround
  obtain ⟨hseq, hεbound⟩ := hround
  have hbase : net.chain.finalizedWith c.address = some ss.state.outcome ∨
      (∃ t, net.chain.statusOf c = .open t ∧ t ≤ ss.state.turnNum) ∨
      (∃ t ch, net.chain.statusOf c = .challenged t ch ∧
        (t < ss.state.turnNum ∨ ch.state = ss.state) ∧ net1.chain.now < ch.deadline) := by
    rcases hst' with ho | ⟨t, ch, hstt, hlt, hdd⟩
    · exact Or.inr (Or.inl ho)
    · exact Or.inr (Or.inr ⟨t, ch, hstt, hlt, lt_of_lt_of_le hεbound hdd⟩)
  have hinv := latest_round_keeps_status A.toBounds hc hp hdur hseq hεbound hlatest hfinal hbase
  rcases hinv with hfz' | ⟨t, hopen, htle⟩ | ⟨t, ch, hchal, hdis, hdd⟩
  · apply UnbeatableIn.done
    show (net1.applyHonest apps (.chain (.challenge c [ss] ss.state))).Finalized c
      ss.state.outcome
    cases hcc : net1.chain.apply apps p (.challenge c [ss] ss.state) with
    | none =>
      simpa [NetworkState.applyHonest, NetworkState.Finalized, hcc, Option.getD_none] using hfz'
    | some s' =>
      simp only [NetworkState.Finalized, NetworkState.applyHonest, hcc, Option.getD_some]
      exact Adjudicator.finalizedWith_apply hcc hfz'
  · have hmode : net1.chain.mode c = .open := by rw [Adjudicator.mode_eq, hopen]; rfl
    have hsucc := challenge_can_happen apps net1.chain p c [ss] ss.state hp
      (by rw [hc]; simp [consensusRules, hchan, hall]) hchan
      (Or.inl ⟨hmode, by rw [hopen]; exact htle⟩)
    have hne : net1.applyHonest apps (.chain (.challenge c [ss] ss.state)) =
        { net1 with
          chain := net1.chain.setStatus c (.challenged ss.state.turnNum
            ⟨ss.state, net1.chain.now + c.challengeDuration⟩) } := by
      simp only [NetworkState.applyHonest, Adjudicator.apply, hsucc, Option.getD_some]
    rw [hne]
    refine finish _ ss.state.turnNum ⟨ss.state, net1.chain.now + c.challengeDuration⟩ rfl le_rfl
      ?_ ?_ hseq.sent_eq
    · show (net1.chain.setStatus c (.challenged ss.state.turnNum
          ⟨ss.state, net1.chain.now + c.challengeDuration⟩)).statusOf c =
        .challenged ss.state.turnNum ⟨ss.state, net1.chain.now + c.challengeDuration⟩
      rw [Adjudicator.statusOf_setStatus, if_pos rfl]
    · show net1.chain.now ≤ net1.chain.now + c.challengeDuration
      exact Nat.le_add_right _ _
  · by_cases hlt : t < ss.state.turnNum
    · have hmode : net1.chain.mode c = .challenge := by
        rw [Adjudicator.mode_eq, hchal, ChannelStatus.mode_challenged, if_neg (not_le.mpr hdd)]
      have hsucc := challenge_can_happen apps net1.chain p c [ss] ss.state hp
        (by rw [hc]; simp [consensusRules, hchan, hall]) hchan
        (Or.inr ⟨hmode, by rw [hchal, ChannelStatus.turnNumRecord_challenged]; exact hlt⟩)
      have hne : net1.applyHonest apps (.chain (.challenge c [ss] ss.state)) =
          { net1 with
            chain := net1.chain.setStatus c (.challenged ss.state.turnNum
              ⟨ss.state, net1.chain.now + c.challengeDuration⟩) } := by
        simp only [NetworkState.applyHonest, Adjudicator.apply, hsucc, Option.getD_some]
      rw [hne]
      refine finish _ ss.state.turnNum ⟨ss.state, net1.chain.now + c.challengeDuration⟩ rfl le_rfl
        ?_ ?_ hseq.sent_eq
      · show (net1.chain.setStatus c (.challenged ss.state.turnNum
            ⟨ss.state, net1.chain.now + c.challengeDuration⟩)).statusOf c =
          .challenged ss.state.turnNum ⟨ss.state, net1.chain.now + c.challengeDuration⟩
        rw [Adjudicator.statusOf_setStatus, if_pos rfl]
      · show net1.chain.now ≤ net1.chain.now + c.challengeDuration
        exact Nat.le_add_right _ _
    · have hchs : ch.state = ss.state := hdis.resolve_left hlt
      have hfail : net1.chain.apply apps p (.challenge c [ss] ss.state) = none := by
        cases hres : net1.chain.apply apps p (.challenge c [ss] ss.state) with
        | none => rfl
        | some s' =>
          exfalso
          obtain ⟨⟨-, -, -, hm⟩, -⟩ := Adjudicator.challenge_some hres
          rw [Adjudicator.mode_eq, hchal] at hm
          simp only [ChannelStatus.mode_challenged, ChannelStatus.turnNumRecord_challenged] at hm
          rcases hm with ⟨hm, -⟩ | ⟨-, hgt⟩
          · split at hm <;> cases hm
          · exact hlt hgt
      have hne : net1.applyHonest apps (.chain (.challenge c [ss] ss.state)) = net1 := by
        simp only [NetworkState.applyHonest, hfail, Option.getD_none]
      rw [hne]
      exact finish net1 t ch hchs (not_lt.mp hlt) hchal (le_of_lt hdd) hseq.sent_eq

/-- One round of adversary play keeps "open at or below `ss.state.turnNum`,
    or challenged below it (or matching it) with the deadline still ahead",
    when `p` has sent nothing of `c` above `ss.state.turnNum` except
    `ss.state` itself, and nothing final at all (`hsent`). The turn-bound
    argument of `latest_round_keeps_status` applies unchanged to `challenge`
    and `checkpoint`; a `conclude` on `c` is excluded outright, not merely
    assigned an outcome, because it needs `p`'s own signature on a final
    state of `c` (`ConclusionProof`, `p ∈ c.participants`), which
    `hbounds.unforgeable` ties to a state in `net.sent` — contradicting
    `hsent`'s `isFinal = false`. Used by `late_observer_can_checkpoint`,
    which (unlike `latest_state_finalizable`) must rule out finalization,
    not merely name its outcome. -/
theorem late_round_keeps_status {apps : Apps E} {p : Participant} {T : Threat E p}
    (hbounds : Bounds apps p T) {c : FixedPart} {ss : SignedState E}
    (hc : apps c.appDef = consensusRules) (hp : p ∈ c.participants)
    (hdur : 2 * T.ε ≤ c.challengeDuration) :
    ∀ {net net' : NetworkState E p} {advs : List (AdvMove E)},
      T.FeasibleSeq apps net advs net' →
      net'.chain.now < net.chain.now + T.ε →
      (∀ t ∈ net.sent, t.state.channel = c →
        (t.state.turnNum < ss.state.turnNum ∨ t.state = ss.state) ∧ t.state.isFinal = false) →
      ((∃ t, net.chain.statusOf c = .open t ∧ t ≤ ss.state.turnNum) ∨
        (∃ t ch, net.chain.statusOf c = .challenged t ch ∧
          (t < ss.state.turnNum ∨ ch.state = ss.state) ∧ net'.chain.now < ch.deadline)) →
      (∃ t, net'.chain.statusOf c = .open t ∧ t ≤ ss.state.turnNum) ∨
      (∃ t ch, net'.chain.statusOf c = .challenged t ch ∧
        (t < ss.state.turnNum ∨ ch.state = ss.state) ∧ net'.chain.now < ch.deadline) := by
  intro net net' advs hseq
  induction hseq with
  | nil => intro _ _ hbase; exact hbase
  | @cons net1 net2 m rest hfeas hrest ih =>
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
    have step : ((∃ t, net1.chain.statusOf c = .open t ∧ t ≤ ss.state.turnNum) ∨
        (∃ t ch, net1.chain.statusOf c = .challenged t ch ∧
          (t < ss.state.turnNum ∨ ch.state = ss.state) ∧ net2.chain.now < ch.deadline)) →
        ((∃ t, (net1.applyAdv apps m).chain.statusOf c = .open t ∧ t ≤ ss.state.turnNum) ∨
        (∃ t ch, (net1.applyAdv apps m).chain.statusOf c = .challenged t ch ∧
          (t < ss.state.turnNum ∨ ch.state = ss.state) ∧ net2.chain.now < ch.deadline)) := by
      intro hbase1
      rcases hbase1 with ⟨t, ho, hle⟩ | ⟨t, ch, hst, hdis, hdd⟩
      · cases m with
        | deliver _ => exact Or.inl ⟨t, ho, hle⟩
        | tick dt =>
          refine Or.inl ⟨t, ?_, hle⟩
          simpa [NetworkState.applyAdv] using ho
        | chain caller op =>
          simp only [NetworkState.applyAdv]
          cases h : net1.chain.apply apps caller op with
          | none => exact Or.inl ⟨t, ho, hle⟩
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
              refine Or.inl ⟨t, ?_, hle⟩
              rw [Adjudicator.statusOf_of_status hs]; exact ho
            | tick dt =>
              have hs' : net1.chain.tick dt = s' := by simpa using h
              subst hs'
              refine Or.inl ⟨t, ?_, hle⟩
              rw [Adjudicator.tick_statusOf]; exact ho
            | transfer a b =>
              by_cases hac : a = c
              · subst hac
                obtain ⟨o, -, -, hfo, -, -, -, -, -, -, -, -⟩ := Adjudicator.transfer_some h
                rw [hfo1] at hfo; exact absurd hfo (by simp)
              · obtain ⟨_, _, _, _, _, _, _, _, hs, _, _, _⟩ := Adjudicator.transfer_some h
                refine Or.inl ⟨t, ?_, hle⟩
                rw [Adjudicator.statusOf_of_status hs, Adjudicator.statusOf_setStatus,
                  if_neg (Ne.symm hac)]
                exact ho
            | reclaim l v =>
              by_cases hlc : l = c
              · subst hlc
                obtain ⟨oL, -, -, -, -, hfo, -, -, -, -, -, -, -, -⟩ := Adjudicator.reclaim_some h
                rw [hfo1] at hfo; exact absurd hfo (by simp)
              · obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hsr, _, _⟩ := Adjudicator.reclaim_some h
                refine Or.inl ⟨t, ?_, hle⟩
                rw [hsr, Adjudicator.statusOf_setStatus, if_neg (Ne.symm hlc)]
                exact ho
            | challenge c' proof cand =>
              by_cases hcc : c' = c
              · subst hcc
                obtain ⟨⟨-, hs, -, -⟩, rfl⟩ := Adjudicator.challenge_some h
                rcases hsupp proof cand hU hs with hlt | heq
                · refine Or.inr ⟨cand.turnNum,
                    Challenge.mk cand (net1.chain.now + c'.challengeDuration),
                    by rw [Adjudicator.statusOf_setStatus, if_pos rfl], Or.inl hlt, ?_⟩
                  have hself : T.ε ≤ 2 * T.ε := by rw [Nat.two_mul]; exact Nat.le_add_left T.ε T.ε
                  have hge : T.ε ≤ c'.challengeDuration := le_trans hself hdur
                  exact lt_of_lt_of_le hεbound (Nat.add_le_add_left hge net1.chain.now)
                · refine Or.inr ⟨cand.turnNum,
                    Challenge.mk cand (net1.chain.now + c'.challengeDuration),
                    by rw [Adjudicator.statusOf_setStatus, if_pos rfl], Or.inr heq, ?_⟩
                  have hself : T.ε ≤ 2 * T.ε := by rw [Nat.two_mul]; exact Nat.le_add_left T.ε T.ε
                  have hge : T.ε ≤ c'.challengeDuration := le_trans hself hdur
                  exact lt_of_lt_of_le hεbound (Nat.add_le_add_left hge net1.chain.now)
              · obtain ⟨-, rfl⟩ := Adjudicator.challenge_some h
                refine Or.inl ⟨t, ?_, hle⟩
                rw [Adjudicator.statusOf_setStatus, if_neg (Ne.symm hcc)]
                exact ho
            | checkpoint c' proof cand =>
              by_cases hcc : c' = c
              · subst hcc
                obtain ⟨⟨-, hs, -, -⟩, rfl⟩ := Adjudicator.checkpoint_some h
                refine Or.inl ⟨cand.turnNum,
                  by rw [Adjudicator.statusOf_setStatus, if_pos rfl], ?_⟩
                rcases hsupp proof cand hU hs with hlt | heq
                · exact le_of_lt hlt
                · exact le_of_eq (by rw [heq])
              · obtain ⟨-, rfl⟩ := Adjudicator.checkpoint_some h
                refine Or.inl ⟨t, ?_, hle⟩
                rw [Adjudicator.statusOf_setStatus, if_neg (Ne.symm hcc)]
                exact ho
            | conclude c' ss' =>
              by_cases hcc : c' = c
              · subst hcc
                obtain ⟨⟨-, hproof'⟩, rfl⟩ := Adjudicator.conclude_some h
                have hp' : p ∈ ss'.signers := hproof'.2.2 p (hproof'.1 ▸ hp)
                have hmem : ss' ∈ (Op.conclude c' ss').proofStates := by simp [Op.proofStates]
                obtain ⟨x, hxmem, hxeq⟩ := hU ss' hmem hp'
                have hnf := (hsent x hxmem (by rw [hxeq]; exact hproof'.1)).2
                have hxfinal : x.state.isFinal = true := by rw [hxeq]; exact hproof'.2.1
                simp [hnf] at hxfinal
              · obtain ⟨-, rfl⟩ := Adjudicator.conclude_some h
                refine Or.inl ⟨t, ?_, hle⟩
                rw [Adjudicator.statusOf_setStatus, if_neg (Ne.symm hcc)]
                exact ho
      · have hmono : net1.chain.now ≤ net2.chain.now :=
          le_trans (NetworkState.applyAdv_now_le apps net1 m) hrest.now_le
        have hltdl : net1.chain.now < ch.deadline := lt_of_le_of_lt hmono hdd
        cases m with
        | deliver _ => exact Or.inr ⟨t, ch, hst, hdis, hdd⟩
        | tick dt =>
          refine Or.inr ⟨t, ch, ?_, hdis, hdd⟩
          simpa [NetworkState.applyAdv] using hst
        | chain caller op =>
          simp only [NetworkState.applyAdv]
          cases h : net1.chain.apply apps caller op with
          | none => exact Or.inr ⟨t, ch, hst, hdis, hdd⟩
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
              refine Or.inr ⟨t, ch, ?_, hdis, hdd⟩
              rw [Adjudicator.statusOf_of_status hs]; exact hst
            | tick dt =>
              have hs' : net1.chain.tick dt = s' := by simpa using h
              subst hs'
              refine Or.inr ⟨t, ch, ?_, hdis, hdd⟩
              rw [Adjudicator.tick_statusOf]; exact hst
            | transfer a b =>
              by_cases hac : a = c
              · subst hac
                obtain ⟨o, -, -, hfo, -, -, -, -, -, -, -, -⟩ := Adjudicator.transfer_some h
                rw [hfo1] at hfo; exact absurd hfo (by simp)
              · obtain ⟨_, _, _, _, _, _, _, _, hs, _, _, _⟩ := Adjudicator.transfer_some h
                refine Or.inr ⟨t, ch, ?_, hdis, hdd⟩
                rw [Adjudicator.statusOf_of_status hs, Adjudicator.statusOf_setStatus,
                  if_neg (Ne.symm hac)]
                exact hst
            | reclaim l v =>
              by_cases hlc : l = c
              · subst hlc
                obtain ⟨oL, -, -, -, -, hfo, -, -, -, -, -, -, -, -⟩ := Adjudicator.reclaim_some h
                rw [hfo1] at hfo; exact absurd hfo (by simp)
              · obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hsr, _, _⟩ := Adjudicator.reclaim_some h
                refine Or.inr ⟨t, ch, ?_, hdis, hdd⟩
                rw [hsr, Adjudicator.statusOf_setStatus, if_neg (Ne.symm hlc)]
                exact hst
            | challenge c' proof cand =>
              by_cases hcc : c' = c
              · subst hcc
                obtain ⟨⟨-, hs, -, -⟩, rfl⟩ := Adjudicator.challenge_some h
                rcases hsupp proof cand hU hs with hlt | heq
                · refine Or.inr ⟨cand.turnNum,
                    Challenge.mk cand (net1.chain.now + c'.challengeDuration),
                    by rw [Adjudicator.statusOf_setStatus, if_pos rfl], Or.inl hlt, ?_⟩
                  have hself : T.ε ≤ 2 * T.ε := by rw [Nat.two_mul]; exact Nat.le_add_left T.ε T.ε
                  have hge : T.ε ≤ c'.challengeDuration := le_trans hself hdur
                  exact lt_of_lt_of_le hεbound (Nat.add_le_add_left hge net1.chain.now)
                · refine Or.inr ⟨cand.turnNum,
                    Challenge.mk cand (net1.chain.now + c'.challengeDuration),
                    by rw [Adjudicator.statusOf_setStatus, if_pos rfl], Or.inr heq, ?_⟩
                  have hself : T.ε ≤ 2 * T.ε := by rw [Nat.two_mul]; exact Nat.le_add_left T.ε T.ε
                  have hge : T.ε ≤ c'.challengeDuration := le_trans hself hdur
                  exact lt_of_lt_of_le hεbound (Nat.add_le_add_left hge net1.chain.now)
              · obtain ⟨-, rfl⟩ := Adjudicator.challenge_some h
                refine Or.inr ⟨t, ch, ?_, hdis, hdd⟩
                rw [Adjudicator.statusOf_setStatus, if_neg (Ne.symm hcc)]
                exact hst
            | checkpoint c' proof cand =>
              by_cases hcc : c' = c
              · subst hcc
                obtain ⟨⟨-, hs, -, -⟩, rfl⟩ := Adjudicator.checkpoint_some h
                refine Or.inl ⟨cand.turnNum,
                  by rw [Adjudicator.statusOf_setStatus, if_pos rfl], ?_⟩
                rcases hsupp proof cand hU hs with hlt | heq
                · exact le_of_lt hlt
                · exact le_of_eq (by rw [heq])
              · obtain ⟨-, rfl⟩ := Adjudicator.checkpoint_some h
                refine Or.inr ⟨t, ch, ?_, hdis, hdd⟩
                rw [Adjudicator.statusOf_setStatus, if_neg (Ne.symm hcc)]
                exact hst
            | conclude c' ss' =>
              by_cases hcc : c' = c
              · subst hcc
                obtain ⟨⟨-, hproof'⟩, rfl⟩ := Adjudicator.conclude_some h
                have hp' : p ∈ ss'.signers := hproof'.2.2 p (hproof'.1 ▸ hp)
                have hmem : ss' ∈ (Op.conclude c' ss').proofStates := by simp [Op.proofStates]
                obtain ⟨x, hxmem, hxeq⟩ := hU ss' hmem hp'
                have hnf := (hsent x hxmem (by rw [hxeq]; exact hproof'.1)).2
                have hxfinal : x.state.isFinal = true := by rw [hxeq]; exact hproof'.2.1
                simp [hnf] at hxfinal
              · obtain ⟨-, rfl⟩ := Adjudicator.conclude_some h
                refine Or.inr ⟨t, ch, ?_, hdis, hdd⟩
                rw [Adjudicator.statusOf_setStatus, if_neg (Ne.symm hcc)]
                exact hst
    have hbase' := step hbase
    have hεbound' : net2.chain.now < (net1.applyAdv apps m).chain.now + T.ε :=
      lt_of_lt_of_le hεbound (Nat.add_le_add_right (NetworkState.applyAdv_now_le apps net1 m) T.ε)
    have hsent' : ∀ t ∈ (net1.applyAdv apps m).sent, t.state.channel = c →
        (t.state.turnNum < ss.state.turnNum ∨ t.state = ss.state) ∧ t.state.isFinal = false := by
      rw [NetworkState.applyAdv_sent]; exact hsent
    exact ih hεbound' hsent' hbase'

/-- ForceMove-B05. ForceMove:1511-1529: "as long as Alice notices Bob's challenge within
    the timeout period, she cannot hurt her position by playing on as though
    still in Collaborative mode ... all the moves made in Collaborative still
    stand." A participant who holds a supported state above the challenge
    state, and signed nothing above it, can bring the record to that turn
    before the deadline, with go-nitro `checkpoint`, and the channel is not
    finalized. The adversary can register that same state as a challenge, so
    the goal does not ask for Open mode. -/
theorem late_observer_can_checkpoint (apps : Apps E) {p : Participant} (T : Threat E p)
    (A : Assumptions apps p T) (net : NetworkState E p) (c : FixedPart) (ss : SignedState E)
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
    (by simpa [HonestMove.Feasible, Op.proofStates] using hh) ?_
  intro advs net1 hround
  obtain ⟨hseq, hεbound⟩ := hround
  have hbase : (∃ t, net.chain.statusOf c = .open t ∧ t ≤ ss.state.turnNum) ∨
      (∃ t ch, net.chain.statusOf c = .challenged t ch ∧
        (t < ss.state.turnNum ∨ ch.state = ss.state) ∧ net1.chain.now < ch.deadline) :=
    Or.inr ⟨t, ch, hst, Or.inl hgt, lt_of_lt_of_le hεbound hnow⟩
  have hinv := late_round_keeps_status A.toBounds hc hp hdur hseq hεbound hsent hbase
  rcases hinv with ⟨t1, hopen1, hle1⟩ | ⟨t1, ch1, hchal1, hdis1, hdd1⟩
  · by_cases hlt1 : t1 < ss.state.turnNum
    · have hmode1 : net1.chain.mode c ≠ .finalized := by
        rw [Adjudicator.mode_eq, hopen1]; simp
      have hsucc := checkpoint_can_happen apps net1.chain c [ss] ss.state hmode1
        (by rw [hc]; simp [consensusRules, hchan, hall]) hchan
        (by rw [hopen1]; exact hlt1)
      apply UnbeatableIn.done
      show (net1.applyHonest apps (.chain (.checkpoint c [ss] ss.state))).chain.mode c ≠
          .finalized ∧
        ss.state.turnNum ≤ ((net1.applyHonest apps
          (.chain (.checkpoint c [ss] ss.state))).chain.statusOf c).turnNumRecord
      simp only [NetworkState.applyHonest, Adjudicator.apply, hsucc.1, Option.getD_some]
      refine ⟨?_, ?_⟩
      · rw [hsucc.2]; decide
      · rw [Adjudicator.statusOf_setStatus, if_pos rfl]; exact le_refl _
    · cases hcc : net1.chain.apply apps p (.checkpoint c [ss] ss.state) with
      | none =>
        apply UnbeatableIn.done
        show (net1.applyHonest apps (.chain (.checkpoint c [ss] ss.state))).chain.mode c ≠
            .finalized ∧
          ss.state.turnNum ≤ ((net1.applyHonest apps
            (.chain (.checkpoint c [ss] ss.state))).chain.statusOf c).turnNumRecord
        simp only [NetworkState.applyHonest, hcc, Option.getD_none]
        refine ⟨?_, ?_⟩
        · rw [Adjudicator.mode_eq, hopen1]; simp
        · rw [hopen1]; exact not_lt.mp hlt1
      | some s' =>
        obtain ⟨⟨-, -, -, ht⟩, -⟩ := Adjudicator.checkpoint_some hcc
        rw [hopen1] at ht
        exact absurd ht hlt1
  · by_cases hlt1 : t1 < ss.state.turnNum
    · have hmode1 : net1.chain.mode c ≠ .finalized := by
        rw [Adjudicator.mode_eq, hchal1, ChannelStatus.mode_challenged, if_neg (not_le.mpr hdd1)]
        decide
      have hsucc := checkpoint_can_happen apps net1.chain c [ss] ss.state hmode1
        (by rw [hc]; simp [consensusRules, hchan, hall]) hchan
        (by rw [hchal1, ChannelStatus.turnNumRecord_challenged]; exact hlt1)
      apply UnbeatableIn.done
      show (net1.applyHonest apps (.chain (.checkpoint c [ss] ss.state))).chain.mode c ≠
          .finalized ∧
        ss.state.turnNum ≤ ((net1.applyHonest apps
          (.chain (.checkpoint c [ss] ss.state))).chain.statusOf c).turnNumRecord
      simp only [NetworkState.applyHonest, Adjudicator.apply, hsucc.1, Option.getD_some]
      refine ⟨?_, ?_⟩
      · rw [hsucc.2]; decide
      · rw [Adjudicator.statusOf_setStatus, if_pos rfl]; exact le_refl _
    · cases hcc : net1.chain.apply apps p (.checkpoint c [ss] ss.state) with
      | none =>
        apply UnbeatableIn.done
        show (net1.applyHonest apps (.chain (.checkpoint c [ss] ss.state))).chain.mode c ≠
            .finalized ∧
          ss.state.turnNum ≤ ((net1.applyHonest apps
            (.chain (.checkpoint c [ss] ss.state))).chain.statusOf c).turnNumRecord
        simp only [NetworkState.applyHonest, hcc, Option.getD_none]
        refine ⟨?_, ?_⟩
        · rw [Adjudicator.mode_eq, hchal1, ChannelStatus.mode_challenged,
            if_neg (not_le.mpr hdd1)]
          decide
        · rw [hchal1, ChannelStatus.turnNumRecord_challenged]; exact not_lt.mp hlt1
      | some s' =>
        obtain ⟨⟨-, -, -, ht⟩, -⟩ := Adjudicator.checkpoint_some hcc
        rw [hchal1, ChannelStatus.turnNumRecord_challenged] at ht
        exact absurd ht hlt1

/-- Nitro-22. Nitro:612-614: "The definition of finalizability excludes the case
    where two different finalizable outcomes are held by different
    participants, as in this case at least one participant's strategy would
    be beatable by the other participant's strategy." -/
theorem finalizable_unique (apps : Apps E) (Ts : Threats E apps) (v : Views E) (hv : v.Consistent)
    (c : FixedPart) (p q : Participant) (hpq : p ≠ q) (Ω Ω' : Outcome E)
    (hp : Finalizable apps (Ts.T p) c Ω (v p)) (hq : Finalizable apps (Ts.T q) c Ω' (v q)) :
    Ω = Ω' := by
  sorry

/-- Nitro-22. Nitro:597-611: "exactly one of the following statements is true
    about a channel χ at any point in time: 1. Finalized outcome ... 2. One
    participant has multiple finalizable outcomes ... 3. Multiple participants
    share one finalizable outcome ... 4. No finalizable outcomes." -/
theorem channel_finalizability_cases (apps : Apps E) (Ts : Threats E apps) (v : Views E)
    (hv : v.Consistent) (c : FixedPart) (p0 : Participant) :
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
    (A : Assumptions apps p T) (net : NetworkState E p) (c : FixedPart) (hp : p ∈ c.participants)
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
    (A : Assumptions apps p T) (net : NetworkState E p) (c : FixedPart) (hp : p ∈ c.participants)
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
    (hv : v.Consistent) (c : FixedPart) (Ω : Outcome E) (vt : State E → State E → Bool)
    (hc : apps c.appDef = forceMoveRules vt) (hsetup : SetupPhaseKeepsOutcome vt c)
    (hvt : SetupPhaseAccepted vt c)
    (hn : 0 < c.n) (hdur : ∀ p, 2 * (Ts.T p).ε ≤ c.challengeDuration) (h : AtFundingPoint v c Ω)
    (hchain : ∀ p, (v p).chain.mode c = .open ∧ (v p).chain.statusOf c = .open 0) :
    UniversallyFinalizable apps Ts v c Ω := by
  sorry

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

/-- Nitro-23, ForceMove-A14. Nitro:637-640: "When a single conclusion proof is known to
    each participant ... the channel is in the concluded state." The
    concluded outcome is universally finalizable. -/
theorem concluded_universally_finalizable (apps : Apps E) (Ts : Threats E apps) (v : Views E)
    (hv : v.Consistent) (c : FixedPart) (Ω : Outcome E) (hc : apps c.appDef = consensusRules)
    (h : Concluded v c Ω)
    (hsent : ∀ p, ∀ t ∈ (v p).sent, t.state.channel = c → t.state.isFinal = true →
      t.state.outcome = Ω)
    (hchain : ∀ p, (v p).chain.finalizedWith c.address = none ∨ (v p).Finalized c Ω)
    (hdur : ∀ p, 2 * (Ts.T p).ε ≤ c.challengeDuration)
    (hpend : ∀ p, (v p).DeadlineAfter c (Ts.T p).ε) :
    UniversallyFinalizable apps Ts v c Ω := by
  intro p hp
  obtain ⟨ss, hh, hproof, hΩ⟩ := h p hp
  exact UnbeatableIn.mono (fun _ _ => trivial)
    (conclusion_proof_finalizable apps (Ts.T p) (Ts.ok p) (v p) c ss Ω hc hp hh hproof hΩ
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

/-- Over a feasible sequence of adversary moves, what `p` has received
    only grows, by induction on `NetworkState.applyAdv_received_subset`. -/
theorem Threat.FeasibleSeq.received_subset {apps : Apps E} {p : Participant} {T : Threat E p}
    {net net' : NetworkState E p} {advs : List (AdvMove E)}
    (h : T.FeasibleSeq apps net advs net') : ∀ r ∈ net.received, r ∈ net'.received := by
  induction h with
  | nil => exact fun r hr => hr
  | @cons net1 net2 m rest _ _ ih =>
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

/-- One round of adversary play keeps `ConsensusSafe`. Any candidate on
    channel `c` that carries `p`'s genuine signature (`ByAll`, consensus app,
    `p ∈ c.participants`) is, via `hbounds.unforgeable`, a state `p` itself
    sent, so `hsent` bounds it: below `ss.state.turnNum`, exactly
    `ss.state`, or at outcome `Ω2` — and, if final, at outcome `Ω1` or `Ω2`
    outright. A `conclude` on `c` always needs a final candidate, so it
    always lands on `Ω1` or `Ω2`. A `checkpoint` on `c` always clears to
    `.open`, safe regardless of its candidate. A fresh `challenge`/
    re-`challenge` on `c` lands at a candidate that is itself safe, or
    strictly below `ss.state.turnNum` with a deadline `c.challengeDuration
    ≥ 2 * T.ε` past the round's own clock — enough to survive this round
    (`hεbound`) with a full round `T.ε` to spare for `p` to answer it.
    Used by `consensus_enabled_outcomes`. -/
theorem consensus_round_safe {apps : Apps E} {p : Participant} {T : Threat E p}
    (hbounds : Bounds apps p T) {c : FixedPart} {ss : SignedState E} {Ω1 Ω2 : Outcome E}
    (hc : apps c.appDef = consensusRules) (hp : p ∈ c.participants) (hΩ1 : ss.state.outcome = Ω1)
    (hdur : 2 * T.ε ≤ c.challengeDuration) :
    ∀ {net net' : NetworkState E p} {advs : List (AdvMove E)},
      T.FeasibleSeq apps net advs net' →
      net'.chain.now < net.chain.now + T.ε →
      (∀ t ∈ net.sent, t.state.channel = c →
        (t.state.turnNum < ss.state.turnNum ∨ t.state = ss.state ∨ t.state.outcome = Ω2) ∧
        (t.state.isFinal = true → t.state.outcome = Ω1 ∨ t.state.outcome = Ω2)) →
      ConsensusSafe c ss Ω1 Ω2 net net' → ConsensusSafe c ss Ω1 Ω2 net' net' := by
  intro net net' advs hseq
  induction hseq with
  | nil => intro _ _ hbase; exact hbase
  | @cons net1 net2 m rest hfeas hrest ih =>
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
      | tick dt =>
        simpa [NetworkState.applyAdv, FixedPart.address_eq] using
          ChannelStatus.finalizedWith_mono (by simpa [FixedPart.address_eq] using hf)
            (Nat.le_add_right _ dt)
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
          | tick dt =>
            have hstatusc' : (net1.applyAdv apps (AdvMove.tick dt : AdvMove E)).chain.statusOf c =
                .open t := by simpa [NetworkState.applyAdv] using ho
            exact Or.inr (Or.inr ⟨by
              simp [FixedPart.address_eq, Adjudicator.finalizedWith_channel, hstatusc'],
              Or.inl ⟨t, hstatusc'⟩⟩)
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
            | tick dt =>
              by_cases hexp2 : ch.deadline ≤ net1.chain.now + dt
              · exact Or.inl (by
                  simp [NetworkState.applyAdv, FixedPart.address_eq,
                    Adjudicator.finalizedWith_channel, Adjudicator.tick_statusOf, hst,
                    ChannelStatus.finalizedWith_challenged, hexp2, h1])
              · refine Or.inr (Or.inr ⟨?_, Or.inr ⟨t, ch, ?_, Or.inl h1⟩⟩)
                · simp [NetworkState.applyAdv, FixedPart.address_eq,
                    Adjudicator.finalizedWith_channel, Adjudicator.tick_statusOf, hst,
                    ChannelStatus.finalizedWith_challenged, hexp2]
                · simpa [NetworkState.applyAdv, Adjudicator.tick_statusOf] using hst
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
            | tick dt =>
              by_cases hexp2 : ch.deadline ≤ net1.chain.now + dt
              · exact Or.inr (Or.inl (by
                  simp [NetworkState.applyAdv, FixedPart.address_eq,
                    Adjudicator.finalizedWith_channel, Adjudicator.tick_statusOf, hst,
                    ChannelStatus.finalizedWith_challenged, hexp2, h2]))
              · refine Or.inr (Or.inr ⟨?_, Or.inr ⟨t, ch, ?_, Or.inr (Or.inl h2)⟩⟩)
                · simp [NetworkState.applyAdv, FixedPart.address_eq,
                    Adjudicator.finalizedWith_channel, Adjudicator.tick_statusOf, hst,
                    ChannelStatus.finalizedWith_challenged, hexp2]
                · simpa [NetworkState.applyAdv, Adjudicator.tick_statusOf] using hst
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
            | tick dt =>
              have hdl : net1.chain.now + dt < ch.deadline := by
                have := hboundM
                simpa [NetworkState.applyAdv, Adjudicator.tick_now] using lt_of_le_of_lt this hddC
              refine Or.inr (Or.inr ⟨?_, Or.inr ⟨t, ch, ?_, Or.inr (Or.inr ⟨hltC, hddC⟩)⟩⟩)
              · simp [NetworkState.applyAdv, FixedPart.address_eq,
                  Adjudicator.finalizedWith_channel, Adjudicator.tick_statusOf, hst,
                  ChannelStatus.finalizedWith_challenged, not_le.mpr hdl]
              · simpa [NetworkState.applyAdv, Adjudicator.tick_statusOf] using hst
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
    have hsent' : ∀ t ∈ (net1.applyAdv apps m).sent, t.state.channel = c →
        (t.state.turnNum < ss.state.turnNum ∨ t.state = ss.state ∨ t.state.outcome = Ω2) ∧
        (t.state.isFinal = true → t.state.outcome = Ω1 ∨ t.state.outcome = Ω2) := by
      rw [NetworkState.applyAdv_sent]; exact hsent
    exact ih hεbound' hsent' hbase'
/-- `p`'s own checkpoint with `ss` keeps `ConsensusSafe`: it either fails
    (leaving `n` unchanged, still safe) or succeeds, clearing any challenge
    on `c` to `.open`, which is safe unconditionally (`ChannelStatus.open`'s
    `finalizedWith` is `none` regardless of the record). Used to show `p`'s
    constant checkpoint strategy keeps `ConsensusSafe` at every round of
    `consensus_enabled_outcomes`'s `Run`. -/
theorem consensus_checkpoint_keeps_safe {apps : Apps E} {p : Participant} {c : FixedPart}
    {ss : SignedState E} {Ω1 Ω2 : Outcome E} (hchan : ss.state.channel = c) (hall : ss.ByAll)
    {n : NetworkState E p} (hbase : ConsensusSafe c ss Ω1 Ω2 n n) :
    ConsensusSafe c ss Ω1 Ω2 (n.applyHonest apps (.chain (.checkpoint c [ss] ss.state)))
      (n.applyHonest apps (.chain (.checkpoint c [ss] ss.state))) := by
  cases hcc : n.chain.apply apps p (.checkpoint c [ss] ss.state) with
  | none =>
    have hne : n.applyHonest apps (.chain (.checkpoint c [ss] ss.state)) = n := by
      simp [NetworkState.applyHonest, hcc]
    rw [hne]; exact hbase
  | some s' =>
    obtain ⟨-, rfl⟩ := Adjudicator.checkpoint_some hcc
    have hne : n.applyHonest apps (.chain (.checkpoint c [ss] ss.state)) =
        { n with chain := n.chain.setStatus c (.open ss.state.turnNum) } := by
      simp [NetworkState.applyHonest, hcc]
    rw [hne]
    refine Or.inr (Or.inr ⟨?_, ss.state.turnNum, ?_⟩)
    · simp [FixedPart.address_eq, Adjudicator.finalizedWith_channel, Adjudicator.statusOf_setStatus]
    · simp [Adjudicator.statusOf_setStatus]


/-- Nitro-49 (consensus game, Nitro:660-688), SATP-08, docs-0020-01. Nitro:684-688:
    "Throughout the only enabled outcomes for any participant are Ω1 and Ω2.
    In particular, a participant has the finalizable outcome [χ ↦ Ω1]_p
    until they approve the transition, and then enabled outcomes
    [χ ↦ Ω1, Ω2]_(p) until they receive the final state." Under the
    consensus app: a participant who holds an all-signed state with `Ω1`,
    signed no other state at that turn or above except with `Ω2`, and signed
    final states only with `Ω1` or `Ω2`, has only `Ω1` and `Ω2` enabled. -/
theorem consensus_enabled_outcomes (apps : Apps E) {p : Participant} (T : Threat E p)
    (A : Assumptions apps p T) (net : NetworkState E p) (c : FixedPart) (ss : SignedState E)
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
  sorry

/-- Nitro-30, Nitro-16. Nitro:775-777: "reasoning about redistribution is easy
    in Turbo: if you can find one strategy to move a certain amount into an
    address, then no-one else can prevent this from occurring." A transfer
    sequence that reaches balance `x` at the external destination `d` gives
    an unbeatable transfer-only strategy against a transfer-only adversary
    (Nitro:779-781). A channel target is excluded: the adversary can pay a
    finalized channel's coins onward in the same round. -/
theorem turbo_redistribution_unbeatable (apps : Apps E) {p : Participant} (T : Threat E p)
    (B : Bounds apps p T) (hT : T.TransfersOnly) (hcap : T.CapableTransfers)
    (net : NetworkState E p) (hdag : net.chain.IsDAG)
    (ops : List (Participant × Op E)) (hops : OnlyTransfers ops) (d : E) (x : Coins)
    (hgoal : x ≤ (Adjudicator.applyAll apps ops net.chain).balances.get (.external d)) :
    CanObtainIn apps T HonestMove.IsTransfer (.external d) x net := by
  sorry

/-- Nitro-31. Nitro:785-787: "a deposit into the system cannot reduce the value of
    any address and cannot increase the value of any address by more than the
    value of the deposit." -/
theorem deposit_bounds_value (apps : Apps E) {p : Participant} (T : Threat E p)
    (A : Assumptions apps p T) (net : NetworkState E p) (c : FixedPart) (d : E) (y x x' : Coins)
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
    (A : Assumptions apps p T) (net : NetworkState E p) (d q : E) (hq : q ≠ d)
    (a : FixedPart) (s' : Adjudicator E) (h : net.chain.transfer a (.external q) = some s')
    (x : Coins) :
    Value apps T d net x ↔ Value apps T d { net with chain := s' } x := by
  sorry

/-- Nitro-32. Nitro:792-794: "While it is technically possible to create outcomes
    with cycles, it is also possible for any participant in the channel to
    prevent this from happening." Under the consensus app a participant who
    signs no state can keep every cycle away from its open channels. -/
theorem participant_can_prevent_cycles (apps : Apps E) {p : Participant} (T : Threat E p)
    (A : Assumptions apps p T) (net : NetworkState E p)
    (hc : ∀ c : FixedPart, p ∈ c.participants → apps c.appDef = consensusRules)
    (hopen : ∀ c : FixedPart, p ∈ c.participants → ∃ t, net.chain.statusOf c = .open t)
    (hdag : net.chain.IsDAG) (hsent : net.sent = []) :
    Prevents apps T (fun net' => ∃ c : FixedPart, p ∈ c.participants ∧
      Relation.TransGen net'.chain.Edge c.address c.address) net := by
  sorry

/-- Nitro-33, Nitro-34, Nitro-32. Nitro:836-837: "it is impossible to find a strategy
    that gives any node a value higher than allocated by this algorithm."
    In the transfer-only game (Nitro:779-781), on a DAG of outcomes. -/
theorem turbo_value_upper_bound (apps : Apps E) {p : Participant} (T : Threat E p)
    (B : Bounds apps p T) (hT : T.TransfersOnly) (hcap : T.CapableTransfers)
    (net : NetworkState E p) (hdag : net.chain.IsDAG) (n : Address E) (v x : Coins)
    (hv : net.chain.TurboValue n v)
    (h : CanObtainIn apps T HonestMove.IsTransfer n x net) : x ≤ v := by
  sorry

/-- Nitro-33, Nitro-35, Nitro-18. Nitro:837-839: "It is also not hard to construct a
    strategy for a node to obtain the value allocated by the algorithm, if
    necessary by actually implementing the algorithm up until that node." In
    the transfer-only game, for an external destination. -/
theorem turbo_value_achievable (apps : Apps E) {p : Participant} (T : Threat E p)
    (B : Bounds apps p T) (hT : T.TransfersOnly) (hcap : T.CapableTransfers)
    (net : NetworkState E p) (hdag : net.chain.IsDAG) (d : E) (v : Coins)
    (hv : net.chain.TurboValue (.external d) v) :
    CanObtainIn apps T HonestMove.IsTransfer (.external d) v net := by
  sorry

/-- Nitro-18, Nitro-33, Nitro-34, Nitro-35. Nitro:482-484 with Nitro:835-839: on a Turbo DAG
    the value at `d` in the transfer-only game is the algorithm's value of
    `d`. -/
theorem turbo_value_is_value (apps : Apps E) {p : Participant} (T : Threat E p)
    (B : Bounds apps p T) (hT : T.TransfersOnly) (hcap : T.CapableTransfers)
    (net : NetworkState E p) (hdag : net.chain.IsDAG) (d : E) (v : Coins)
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
    (hv : v.Consistent) (w : LedgerWithSub E) (hw : w.Holds apps Ts v)
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
    (hv : v.Consistent) (hv' : v'.Consistent) (A B : Participant) (dA dB : E) (L χ : FixedPart)
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
    (hv : v.Consistent) (hv' : v'.Consistent) (w : LedgerWithSub E) (a' b' : Coins)
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

/-- Nitro-49 (Nitro:997-1047, §5.4.4 Partial Withdrawal from a Ledger Channel).
    Nitro:1046-1047: "A was able to withdraw their funds instantly, without
    having to wait for the channel timeout." With the conclusion proof for
    `[L ↦ (L' : a + b + c, A : a')]_{A,B}` and `⟦L : x⟧`, `A` obtains `a'`
    at `dA` with no wait, and `L'` is funded with `a + b + c` for `A` and
    `B`. `L'` cannot finalize before `L` pays it: no running challenge of
    `L'` ends within `2 * ε`, no participant signed a final state of `L'`,
    and a challenge of `L'` lasts at least `2 * ε`. -/
theorem ledger_partial_withdrawal (apps : Apps E) (Ts : Threats E apps) (v : Views E)
    (hv : v.Consistent) (A B : Participant) (dA dB : E) (L L' χ : FixedPart) (a b c a' : Coins)
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
  sorry

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
  sorry

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
    (hdur : 2 * T.ε ≤ r.V.challengeDuration) (net : NetworkState E p) (s1 : SignedState E)
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
    (net : NetworkState E P) (hHm : HoldsLatestLedger net Lm om) (hHp : HoldsLatestLedger net Lp op)
    (hVs : HoldsVirtualSetup net r alice bob true)
    (hpend : net.DeadlineAfter Lm T.ε ∧ net.DeadlineAfter Lp T.ε ∧ net.DeadlineAfter r.V T.ε)
    (hchain : net.chain.finalizedWith Lm.address = none ∧
      net.chain.finalizedWith Lp.address = none ∧ net.chain.finalizedWith r.V.address = none) :
    Unbeatable apps T (IntermediaryRecovered r Lm Lp balm balp
      (net.chain.balances.get (.external (r.dest P)))) net := by
  sorry

/-- SATP-20 (Theorem 3.2, Case 1-2, SATP:522-537). An intermediary that has not
    signed any ledger update with a guarantee for `V` keeps its ledger
    balances: "Without Pi's signature on such an update, the consensus app
    guarantees there is no risk to Pi's balances". -/
theorem satp_intermediary_before_round2 (apps : Apps E) {P : Participant} (T : Threat E P)
    (A : Assumptions apps P T) (r : Route E) (hr : r.WellFormed apps) (i : Nat) (hi : 1 ≤ i)
    (hin : i + 1 < r.peers.length) (hP : r.peers[i]? = some P)
    (Lm Lp : FixedPart) (hLm : r.ledgers[i - 1]? = some Lm) (hLp : r.ledgers[i]? = some Lp)
    (hdur : 2 * T.ε ≤ Lm.challengeDuration ∧ 2 * T.ε ≤ Lp.challengeDuration)
    (om op : Allocation E) (balm balp : Coins)
    (hom : r.LedgerBeforeRound2 om P balm) (hop : r.LedgerBeforeRound2 op P balp)
    (net : NetworkState E P) (hHm : HoldsLatestLedger net Lm om) (hHp : HoldsLatestLedger net Lp op)
    (hpend : net.DeadlineAfter Lm T.ε ∧ net.DeadlineAfter Lp T.ε)
    (hchain : net.chain.finalizedWith Lm.address = none ∧
      net.chain.finalizedWith Lp.address = none) :
    Unbeatable apps T (IntermediaryRecovered r Lm Lp balm balp
      (net.chain.balances.get (.external (r.dest P)))) net := by
  sorry

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
    (net : NetworkState E P) (hH : HoldsLatestLedger net L0 o)
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
