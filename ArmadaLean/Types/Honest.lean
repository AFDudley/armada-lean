/-
  The signing rules of an honest participant, as one type (`HonestSend`).
  Each rule about what an honest
  participant signs is one field of one structure. The honest strategy makes
  a signed state only through a reaction's sends
  (`NetworkState.applyHonest`, `Strategy.lean`), and a reaction is feasible
  only when every send satisfies `HonestSend` (`Reaction.SendsHonest`,
  `HonestMove.Feasible`). One invariant over the reachable states proves the
  rules for every state `p` signed (`Nitro.participant_sent_honest`,
  `Reachable.lean`). The rule is defined once,
  and it is proved once, where the signed state is made.

  The rules replace four premises that single theorems carried before:
  * `noConflict`: the premise `MadeNoAlternativeSetupMoves` of
    `funding_point_universally_finalizable`; see
    the funding-point alternative-moves analysis. The participant
    commits no own-violation of kind (a) (`OwnViolation.Conflict`,
    `ArmadaLean/Types/OwnViolation.lean`;
    own-violation is one rule for every participant). It never signs two
    states of one channel at one slot with two outcomes. Every setup turn
    is one slot, so below the funding point every state it signs on a
    channel, final or not, carries the setup outcome (ForceMove:1094,
    ForceMove:1112-1114, ForceMove:1155-1161, ForceMove:1208;
    `State.signSlot_setup`). It replaces the earlier rules `setupOutcome`
    (setup turns only) and `noAlternative` (one state per setup turn), which
    did not cover a final setup state with another outcome
    (`docs/counterexamples/funding_point_universally_finalizable_conclude.lean`).
  * `guaranteesExternal`: the premise `hog` (the type `GuaranteedOutcome`) of
    `satp_end_user_recovers` (counterexample in
    `docs/counterexamples/satp_end_user_recovers.lean`), and
    the same fact for the ledger outcomes `om`/`op` that `satp_theorem_3_2`
    needs (an adversary's unrelated guarantee with a channel peer corrupts the
    guarantee for `V` with a reclaim, `Allocation.addTo`). SATP Protocol 3.1
    Round 2 (SATP:411-418) has each peer sign `G(a0 + b0, [P_i, P_{i+1}])`.
  * `fundsCommitted`: the premise `hR1` of `satp_theorem_3_2` (SATP:409, "Proceed when s0 is committed"; Definition
    3.1, SATP:394-399).
  * `movesFrom`: above the funding point, the
    participant signs a state only as a move from a supported state that it
    holds, at the turn before, and only a move by the rules: with its held
    states and the new state, the rules support the new state
    (ForceMove:744-778: a move is a valid transition from the current
    state). Signing a state with no support that it holds is the
    defender-side own-violation. The setup states (turns below the funding
    point) are excepted, as the protocol defines them (ForceMove:1092-1125).
  * `oneState` (Main's decision, 2026-11-02): the participant signs at most
    one state per turn number of a channel. Re-signing the identical state is
    allowed. This is ForceMove's rule that a participant never signs two
    different states with the same turn number. Without it, a final state
    and a non-final state at one turn break Nitro-24
    (`docs/counterexamples/final_branch.lean`). The rule binds the honest
    participant only; the adversary may sign two states at one turn.
  * `finalLast` (Main's decision, 2026-11-02): after the participant signs
    a final state of a channel, it signs only final states of that channel.
    An honest party that agreed to close does not continue the game; go-nitro
    concludes after a final state. The rule reads "after" by turn number:
    every non-final state of the channel that the participant signs has a
    lower turn than every final state of the channel that it signs. Without
    it, a final proposal that the participant countersigns, followed by play
    from another state at that turn, breaks Nitro-24
    (`docs/counterexamples/final_proposal.lean`). The rule binds the honest
    participant only.

  The type takes the signer's record as three arguments, not a
  `NetworkState`: `Strategy.lean` (which defines `NetworkState`) imports this
  module, because `HonestMove.Feasible` reads `HonestSend`.
-/
import ArmadaLean.Nitro.Lemmas
import ArmadaLean.Types.OwnViolation
import Mathlib.Tactic.Says

namespace ArmadaLean.Nitro

variable {E : Type} [DecidableEq E]

/-- Every guarantee entry of `o` lists only external peers, never a channel.
    The rule `HonestSend.guaranteesExternal` (this module's header). -/
def Allocation.GuaranteesExternal (o : Allocation E) : Prop :=
  ∀ e ∈ o, ∀ x ps, e.item = .guarantee x ps → ∀ d ∈ ps, d.isExternal = true

/-- `Entry.GuaranteesExternal`, restated by matching on `e.item` instead of
    quantifying over every `x`/`ps` it could equal: decidable, since the
    quantifier then ranges over the one list `ps` the match already names. -/
private def Entry.GuaranteesExternalB (e : Entry E) : Bool :=
  match e.item with
  | .guarantee _ ps => ps.all (·.isExternal)
  | .alloc _ => true

omit [DecidableEq E] in
private theorem entry_guaranteesExternal_iff (e : Entry E) :
    (∀ x ps, e.item = .guarantee x ps → ∀ d ∈ ps, d.isExternal = true) ↔
      e.GuaranteesExternalB = true := by
  unfold Entry.GuaranteesExternalB
  cases h : e.item with
  | alloc a => (simp? says simp only [reduceCtorEq, IsEmpty.forall_iff, implies_true])
  | guarantee x ps => (simp? [List.all_eq_true] says simp only [Item.guarantee.injEq, and_imp, forall_apply_eq_imp_iff, forall_eq', List.all_eq_true])

instance (o : Allocation E) : Decidable o.GuaranteesExternal :=
  decidable_of_iff (∀ e ∈ o, e.GuaranteesExternalB = true)
    (forall_congr' fun e => forall_congr' fun _ => (entry_guaranteesExternal_iff e).symm)

/-- The rule `HonestSend.fundsCommitted`: every virtual channel `V` that the
    allocation of `st` names satisfies `prefundHeld` (SATP:409). -/
abbrev HonestSend.FundsCommitted (prefundHeld : FixedPart → Prop) (st : State E) : Prop :=
  ∀ V : FixedPart, V.kind = .virtual → st.outcome.entries.find V.address ≠ none → prefundHeld V

/-- The rule `HonestSend.oneState` fails: `signed` holds another state of the
    channel of `st` at the turn of `st`. -/
def HonestSend.TwoAtTurn (signed : List (SignedState E)) (st : State E) : Prop :=
  ∃ s ∈ signed, s.state.channel = st.channel ∧ s.state.turnNum = st.turnNum ∧ s.state ≠ st

instance (signed : List (SignedState E)) (st : State E) :
    Decidable (HonestSend.TwoAtTurn signed st) :=
  inferInstanceAs (Decidable (∃ s ∈ signed, _))

/-- `a` is a final state at a turn no later than the non-final state `b`. -/
def HonestSend.FinalBefore (a b : State E) : Prop :=
  a.isFinal = true ∧ b.isFinal = false ∧ a.turnNum ≤ b.turnNum

instance (a b : State E) : Decidable (HonestSend.FinalBefore a b) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- The rule `HonestSend.finalLast` fails: `signed` holds a state of the
    channel of `st` that is final at a turn no later than the non-final `st`,
    or non-final at a turn no earlier than the final `st`. -/
def HonestSend.AfterFinal (signed : List (SignedState E)) (st : State E) : Prop :=
  ∃ s ∈ signed, s.state.channel = st.channel ∧
    (HonestSend.FinalBefore s.state st ∨ HonestSend.FinalBefore st s.state)

instance (signed : List (SignedState E)) (st : State E) :
    Decidable (HonestSend.AfterFinal signed st) :=
  inferInstanceAs (Decidable (∃ s ∈ signed, _))

/-- **The signing rules for one state `st` that the honest participant
    sends.** `signed` is every state the participant has signed, `st`'s own
    send included. `prefundHeld V` says that the participant holds an
    all-signed pre-fund (turn 0) state of `V` (`NetworkState.HoldsPrefund`,
    `Strategy.lean`). `canMove st` says that the participant holds a
    support of a state of the channel of `st` at the turn before, and that
    its held states and `st` support `st` (`NetworkState.CanMoveTo`,
    `Strategy.lean`). Each field is one rule of this module's header. -/
structure HonestSend (signed : List (SignedState E)) (prefundHeld : FixedPart → Prop)
    (canMove : State E → Prop) (st : State E) : Prop where
  /-- The participant commits no own-violation of kind (a): it signs no two
      states of one channel at one slot with two outcomes
      (`OwnViolation.Conflict`; ForceMove:782-794, ForceMove:1112-1114,
      ForceMove:1208). -/
  noConflict : ¬ OwnViolation.Conflict signed st
  /-- Every guarantee the participant signs names only external peers
      (SATP:411-418). -/
  guaranteesExternal : st.outcome.entries.GuaranteesExternal
  /-- The participant signs an allocation with an entry for a virtual
      channel `V` only when it holds the all-signed pre-fund state of `V`
      (SATP:409). -/
  fundsCommitted : HonestSend.FundsCommitted prefundHeld st
  /-- Above the funding point, the participant signs a state only as a move
      by the rules from a supported state of the same channel at the turn
      before, which it holds (ForceMove:744-778). -/
  movesFrom : st.channel.n ≤ st.turnNum → canMove st
  /-- The participant signs at most one state per turn number of a channel
      (ForceMove: a participant never signs two different states with the
      same turn number; Main's decision 2026-11-02). -/
  oneState : ¬ HonestSend.TwoAtTurn signed st
  /-- After the participant signs a final state of a channel, it signs only
      final states of that channel, by turn number (Main's decision
      2026-11-02). -/
  finalLast : ¬ HonestSend.AfterFinal signed st

namespace HonestSend

/-- Two states that the participant signed on one channel at one slot carry
    one outcome. -/
theorem outcome_eq {signed : List (SignedState E)} {held : FixedPart → Prop}
    {sup : State E → Prop} {st : State E}
    (h : HonestSend signed held sup st) : ∀ s ∈ signed, s.state.channel = st.channel →
    s.state.signSlot = st.signSlot → s.state.outcome = st.outcome := fun s hs hc hslot =>
  Classical.byContradiction fun hne => h.noConflict ⟨s, hs, hc, hslot, hne⟩

/-- A state that satisfies the rules against `prior` with no held pre-fund
    state (so it funds no virtual channel) satisfies them against any
    `signed` whose states are `st` itself or states of `prior`. -/
theorem of_prior {prior signed : List (SignedState E)} {held : FixedPart → Prop}
    {sup : State E → Prop} {st : State E}
    (hst : HonestSend prior (fun _ => False) sup st)
    (hcover : ∀ s ∈ signed, s.state = st ∨ ∃ s' ∈ prior, s'.state = s.state) :
    HonestSend signed held sup st := by
  refine ⟨fun ⟨s, hs, hc, hslot, hne⟩ => ?_, hst.guaranteesExternal,
    fun V hV hf => (hst.fundsCommitted V hV hf).elim, hst.movesFrom,
    fun ⟨s, hs, hc, ht, hne⟩ => ?_, fun ⟨s, hs, hc, hfb⟩ => ?_⟩
  · rcases hcover s hs with h | ⟨s', hs', heq⟩
    · exact hne (by rw [h])
    · rw [← heq] at hc hslot hne
      exact hne (hst.outcome_eq s' hs' hc hslot)
  · rcases hcover s hs with h | ⟨s', hs', heq⟩
    · exact hne h
    · rw [← heq] at hc ht hne
      exact hst.oneState ⟨s', hs', hc, ht, hne⟩
  · rcases hcover s hs with h | ⟨s', hs', heq⟩
    · rw [h] at hfb
      rcases hfb with ⟨h1, h2, -⟩ | ⟨h1, h2, -⟩ <;> rw [h1] at h2 <;> cases h2
    · rw [← heq] at hc hfb
      exact hst.finalLast ⟨s', hs', hc, hfb⟩

end HonestSend

namespace HonestSend

/-- The rules survive a smaller signed record and larger sets of held
    pre-fund states and of possible moves: `noConflict`, `oneState` and
    `finalLast` read `signed` only under `∃`, and `fundsCommitted` and
    `movesFrom` conclude `prefundHeld` and `canMove`. -/
theorem mono {signed signed' : List (SignedState E)} {held held' : FixedPart → Prop}
    {sup sup' : State E → Prop}
    {st : State E} (hsigned : ∀ s ∈ signed', s ∈ signed) (hheld : ∀ V, held V → held' V)
    (hsup : ∀ s, sup s → sup' s)
    (h : HonestSend signed held sup st) : HonestSend signed' held' sup' st :=
  ⟨fun ⟨s, hs, hrest⟩ => h.noConflict ⟨s, hsigned s hs, hrest⟩, h.guaranteesExternal,
    fun V hV hf => hheld V (h.fundsCommitted V hV hf), fun hn => hsup _ (h.movesFrom hn),
    fun ⟨s, hs, hrest⟩ => h.oneState ⟨s, hsigned s hs, hrest⟩,
    fun ⟨s, hs, hrest⟩ => h.finalLast ⟨s, hsigned s hs, hrest⟩⟩

/-- A state whose allocation names no virtual channel (every destination is
    `Address.fundable`: external, or a ledger channel) funds no virtual
    channel, so `fundsCommitted` holds with no held pre-fund state. -/
theorem fundsCommitted_of_fundable {held : FixedPart → Prop} {st : State E}
    (hfund : ∀ e ∈ st.outcome.entries, e.dest.fundable = true) : FundsCommitted held st := by
  intro V hV hf
  obtain ⟨e, he⟩ := Option.ne_none_iff_exists'.mp hf
  have hmem : e ∈ st.outcome.entries := List.mem_of_find?_eq_some he
  have hdest : e.dest = V.address := Allocation.find_dest he
  have hx := hfund e hmem
  rw [hdest, FixedPart.address_eq] at hx
  simp only [Address.fundable, hV, reduceCtorEq, decide_false, Bool.false_eq_true] at hx

end HonestSend

end ArmadaLean.Nitro
