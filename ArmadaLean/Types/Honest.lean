/-
  The signing rules of an honest participant, as one type (`HonestSend`).
  Operator ruling 2026-11-01 (option A): each rule about what an honest
  participant signs is one field of one structure. The honest strategy makes
  a signed state only through a reaction's sends
  (`NetworkState.applyHonest`, `Strategy.lean`), and a reaction is feasible
  only when every send satisfies `HonestSend` (`Reaction.SendsHonest`,
  `HonestMove.Feasible`). One invariant over the reachable states proves the
  rules for every state `p` signed (`Nitro.participant_sent_honest`,
  `Reachable.lean`). Type doctrine rules 1 and 4
  (`armada-laconic/docs/lean/type-doctrine.md`): the rule is defined once,
  and it is proved once, where the signed state is made.

  The rules replace four premises that single theorems carried before:
  * `setupOutcome`: the premise `MadeNoAlternativeSetupMoves` of
    `funding_point_universally_finalizable` (operator rulings 2026-10-31 and
    2026-11-01, armada-laconic
    `labbook/2026-10-31-funding-point-alternative-moves.md`). Below the
    funding point, every state the participant signs on a channel, final or
    not, carries the setup outcome (ForceMove:1094, ForceMove:1112-1114,
    ForceMove:1155-1161, ForceMove:1208). It replaces the earlier rule
    `noAlternative` (one state per setup turn), which did not cover a final
    setup state with another outcome
    (`docs/counterexamples/funding_point_universally_finalizable_conclude.lean`).
  * `guaranteesExternal`: the premise `hog` (the type `GuaranteedOutcome`) of
    `satp_end_user_recovers` (operator ruling 2026-10-31, `aln-223`
    counterexample, `docs/counterexamples/satp_end_user_recovers.lean`), and
    the same fact for the ledger outcomes `om`/`op` that `satp_theorem_3_2`
    needs (an adversary's unrelated guarantee with a channel peer corrupts the
    guarantee for `V` with a reclaim, `Allocation.addTo`). SATP Protocol 3.1
    Round 2 (SATP:411-418) has each peer sign `G(a0 + b0, [P_i, P_{i+1}])`.
  * `fundsCommitted`: the premise `hR1` of `satp_theorem_3_2` (operator
    ruling 2026-10-31; SATP:409, "Proceed when s0 is committed"; Definition
    3.1, SATP:394-399).

  The type takes the signer's record as two arguments, not a `NetworkState`:
  `Strategy.lean` (which defines `NetworkState`) imports this module, because
  `HonestMove.Feasible` reads `HonestSend`.
-/
import ArmadaLean.Nitro.Lemmas
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

/-- The rule `HonestSend.setupOutcome`: below the funding point
    (`turnNum < n`), every state in `signed` of the channel of `st`, also
    below the funding point, has the outcome of `st`. So all the setup
    states that the participant signs on one channel, final or not, carry
    one outcome: the setup outcome.

    ForceMove:1112-1114: "Each player's PREFUNDSETUP state must have the
    same game attributes a0 and resolution r0". ForceMove:1094 and
    ForceMove:1155-1161: every setup transition, a CONCLUDE included,
    requires `s2.resolution == s1.resolution`. ForceMove:1208: "If a player
    transitions from either a PREFUNDSETUP or POSTFUNDSETUP state, s, to a
    CONCLUDE state, s′, we require the resolution to match." Alternative
    moves with the same outcome stay allowed (ForceMove §3.1.5,
    ForceMove:783-784; operator ruling 2026-10-31). go-nitro's unanimous
    `conclude` checks no transition, so the rule is a rule of the honest
    signer, not of the adjudicator. The rule reads every pair in both
    directions, so it holds whichever state of the pair the participant
    signs first (`Nitro.participant_sent_honest`). -/
abbrev HonestSend.SetupOutcome (signed : List (SignedState E)) (st : State E) : Prop :=
  st.turnNum < st.channel.n → ∀ s ∈ signed, s.state.channel = st.channel →
    s.state.turnNum < st.channel.n → s.state.outcome = st.outcome

/-- The rule `HonestSend.fundsCommitted`: every virtual channel `V` that the
    allocation of `st` names satisfies `prefundHeld` (SATP:409). -/
abbrev HonestSend.FundsCommitted (prefundHeld : FixedPart → Prop) (st : State E) : Prop :=
  ∀ V : FixedPart, V.kind = .virtual → st.outcome.entries.find V.address ≠ none → prefundHeld V

/-- **The signing rules for one state `st` that the honest participant
    sends.** `signed` is every state the participant has signed, `st`'s own
    send included. `prefundHeld V` says that the participant holds an
    all-signed pre-fund (turn 0) state of `V` (`NetworkState.HoldsPrefund`,
    `Strategy.lean`). Each field is one rule of this module's header. -/
structure HonestSend (signed : List (SignedState E)) (prefundHeld : FixedPart → Prop)
    (st : State E) : Prop where
  /-- Below the funding point (`turnNum < n`), every state of the channel
      that the participant signs, final or not, carries the setup outcome
      (ForceMove:1112-1114, ForceMove:1208). -/
  setupOutcome : HonestSend.SetupOutcome signed st
  /-- Every guarantee the participant signs names only external peers
      (SATP:411-418). -/
  guaranteesExternal : st.outcome.entries.GuaranteesExternal
  /-- The participant signs an allocation with an entry for a virtual
      channel `V` only when it holds the all-signed pre-fund state of `V`
      (SATP:409). -/
  fundsCommitted : HonestSend.FundsCommitted prefundHeld st

namespace HonestSend

/-- A state that satisfies the rules against `prior` with no held pre-fund
    state (so it funds no virtual channel) satisfies them against any
    `signed` whose states are `st` itself or states of `prior`. -/
theorem of_prior {prior signed : List (SignedState E)} {held : FixedPart → Prop} {st : State E}
    (hst : HonestSend prior (fun _ => False) st)
    (hcover : ∀ s ∈ signed, s.state = st ∨ ∃ s' ∈ prior, s'.state = s.state) :
    HonestSend signed held st := by
  refine ⟨fun hlt s hs hc ht => ?_, hst.guaranteesExternal,
    fun V hV hf => (hst.fundsCommitted V hV hf).elim⟩
  rcases hcover s hs with h | ⟨s', hs', heq⟩
  · rw [h]
  · rw [← heq] at hc ht ⊢
    exact hst.setupOutcome hlt s' hs' hc ht

end HonestSend

namespace HonestSend

/-- The rules survive a smaller signed record and a larger set of held
    pre-fund states: `setupOutcome` reads `signed` only under `∀`, and
    `fundsCommitted` concludes `prefundHeld`. -/
theorem mono {signed signed' : List (SignedState E)} {held held' : FixedPart → Prop}
    {st : State E} (hsigned : ∀ s ∈ signed', s ∈ signed) (hheld : ∀ V, held V → held' V)
    (h : HonestSend signed held st) : HonestSend signed' held' st :=
  ⟨fun hlt s hs => h.setupOutcome hlt s (hsigned s hs), h.guaranteesExternal,
    fun V hV hf => hheld V (h.fundsCommitted V hV hf)⟩

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
