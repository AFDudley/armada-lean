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
  * `noAlternative`: the premise `MadeNoAlternativeSetupMoves` of
    `funding_point_universally_finalizable` (operator ruling 2026-10-31,
    armada-laconic `labbook/2026-10-31-funding-point-alternative-moves.md`;
    ForceMove:783-784, "Alternative moves").
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
  | alloc a => simp
  | guarantee x ps => simp [List.all_eq_true]

instance (o : Allocation E) : Decidable o.GuaranteesExternal :=
  decidable_of_iff (∀ e ∈ o, e.GuaranteesExternalB = true)
    (forall_congr' fun e => forall_congr' fun _ => (entry_guaranteesExternal_iff e).symm)

/-- **The signing rules for one state `st` that the honest participant
    sends.** `signed` is every state the participant has signed, `st`'s own
    send included. `prefundHeld V` says that the participant holds an
    all-signed pre-fund (turn 0) state of `V` (`NetworkState.HoldsPrefund`,
    `Strategy.lean`). Each field is one rule of this module's header. -/
structure HonestSend (signed : List (SignedState E)) (prefundHeld : FixedPart → Prop)
    (st : State E) : Prop where
  /-- Below the funding point (`turnNum < n`), the participant signs no second
      state of the channel at the same turn (ForceMove:783-784). -/
  noAlternative : st.turnNum < st.channel.n → ∀ s ∈ signed, s.state.channel = st.channel →
    s.state.turnNum = st.turnNum → s.state = st
  /-- Every guarantee the participant signs names only external peers
      (SATP:411-418). -/
  guaranteesExternal : st.outcome.entries.GuaranteesExternal
  /-- The participant signs an allocation with an entry for a virtual
      channel `V` only when it holds the all-signed pre-fund state of `V`
      (SATP:409). -/
  fundsCommitted : ∀ V : FixedPart, V.kind = .virtual → st.outcome.entries.find V.address ≠ none →
    prefundHeld V

namespace HonestSend

/-- The rules survive a smaller signed record and a larger set of held
    pre-fund states: `noAlternative` reads `signed` only under `∀`, and
    `fundsCommitted` concludes `prefundHeld`. -/
theorem mono {signed signed' : List (SignedState E)} {held held' : FixedPart → Prop}
    {st : State E} (hsigned : ∀ s ∈ signed', s ∈ signed) (hheld : ∀ V, held V → held' V)
    (h : HonestSend signed held st) : HonestSend signed' held' st :=
  ⟨fun hlt s hs => h.noAlternative hlt s (hsigned s hs), h.guaranteesExternal,
    fun V hV hf => hheld V (h.fundsCommitted V hV hf)⟩

/-- A state whose allocation names no virtual channel (every destination is
    `Address.fundable`: external, or a ledger channel) funds no virtual
    channel, so `fundsCommitted` holds with no held pre-fund state. -/
theorem fundsCommitted_of_fundable {held : FixedPart → Prop} {st : State E}
    (hfund : ∀ e ∈ st.outcome.entries, e.dest.fundable = true) :
    ∀ V : FixedPart, V.kind = .virtual → st.outcome.entries.find V.address ≠ none → held V := by
  intro V hV hf
  obtain ⟨e, he⟩ := Option.ne_none_iff_exists'.mp hf
  have hmem : e ∈ st.outcome.entries := List.mem_of_find?_eq_some he
  have hdest : e.dest = V.address := Allocation.find_dest he
  have hx := hfund e hmem
  rw [hdest, FixedPart.address_eq] at hx
  simp only [Address.fundable, hV, reduceCtorEq, decide_false, Bool.false_eq_true] at hx

end HonestSend

end ArmadaLean.Nitro
