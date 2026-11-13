/-
  Own-violations: a signer signs against its own interest. Design decision
  2026-11-01: own-violation is one rule for every participant, defender and
  attacker. A state signed against the signer's own interest costs only the
  signer, and it never defeats another participant's guarantee.

  Two kinds, defined once here:
  * `OwnViolation.Conflict` (a): the signer signs two states of one channel
    at one slot with two outcomes. The slot is the turn, with every setup
    turn below the funding point merged into one slot (`State.signSlot`).
    So the rule also covers the setup rule of ForceMove: every setup state,
    final or not, carries the setup outcome (ForceMove:1094,
    ForceMove:1112-1114, ForceMove:1155-1161, ForceMove:1208). Above the
    funding point it forbids alternative moves with two outcomes
    (ForceMove:782-794).
  * `OwnViolation.Gift` (b): the signer signs a state that pays its own
    destination less than the state of the turn before, which it holds. A
    state that every participant signed is an agreement (a trade), not a
    gift.

  The honest signer keeps rule (a) (`HonestSend.noConflict`,
  `ArmadaLean/Types/Honest.lean`).
-/
import ArmadaLean.Nitro.Lemmas

namespace ArmadaLean.Nitro

variable {E : Type} [DecidableEq E]

/-- The amount that an outcome pays the external destination `d`: the first
    entry for `d` (`Allocation.owed`). -/
def share (Ω : Outcome E) (d : E) : Coins := Ω.entries.owed (.external d)

/-- The slot of a state for the rule `OwnViolation.Conflict`: its turn, with
    every setup turn below the funding point (`turnNum < n`) merged into
    slot 0. ForceMove:1112-1114: "Each player's PREFUNDSETUP state must have
    the same game attributes a0 and resolution r0". -/
def State.signSlot (s : State E) : Nat := if s.turnNum < s.channel.n then 0 else s.turnNum

/-- Two states below the funding points of their channels share slot 0. -/
theorem State.signSlot_setup {s st : State E}
    (h : s.turnNum < s.channel.n ∧ st.turnNum < st.channel.n) : s.signSlot = st.signSlot := by
  unfold State.signSlot
  rw [if_pos h.1, if_pos h.2]

/-- Own-violation (a): `signed` (states of one signer) holds a state of the
    channel of `st`, at the slot of `st`, with another outcome. -/
def OwnViolation.Conflict (signed : List (SignedState E)) (st : State E) : Prop :=
  ∃ s ∈ signed, s.state.channel = st.channel ∧ s.state.signSlot = st.signSlot ∧
    s.state.outcome ≠ st.outcome

instance (signed : List (SignedState E)) (st : State E) :
    Decidable (OwnViolation.Conflict signed st) :=
  inferInstanceAs (Decidable (∃ s ∈ signed, _))

/-- Own-violation (b), the gift: `known` holds the state of the turn before
    `st` on its channel, and `st` pays the destination `d` of the signer less
    than that state does. -/
def OwnViolation.Gift (d : E) (known : List (SignedState E)) (st : State E) : Prop :=
  ∃ prev ∈ known, prev.state.channel = st.channel ∧ prev.state.turnNum + 1 = st.turnNum ∧
    share st.outcome d < share prev.state.outcome d

instance (d : E) (known : List (SignedState E)) (st : State E) :
    Decidable (OwnViolation.Gift d known st) :=
  inferInstanceAs (Decidable (∃ prev ∈ known, _))

/-- **The own-violation of a signer `q`** with the destination map `dest`,
    for a signed state `ss` that `q` signs: (a) `q` already signed, in
    `known`, a state of the same channel and slot with another outcome, or
    (b) not every participant signed `ss`, and `ss` is a gift of `q` against
    the state of the turn before in `known`. Design decisions 2026-11-01
    and 2026-11-02. -/
def OwnViolation (dest : Participant → E) (q : Participant) (known : List (SignedState E))
    (ss : SignedState E) : Prop :=
  OwnViolation.Conflict (known.filter fun s => decide (q ∈ s.signers)) ss.state ∨
    (¬ ss.ByAll ∧ OwnViolation.Gift (dest q) known ss.state)

instance (dest : Participant → E) (q : Participant) (known : List (SignedState E))
    (ss : SignedState E) : Decidable (OwnViolation dest q known ss) :=
  inferInstanceAs (Decidable (_ ∨ (_ ∧ _)))

end ArmadaLean.Nitro
