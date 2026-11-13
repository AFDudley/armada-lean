/-
  Refined channel types. `docs/lean/typed-library.md` §4, row `Channel.lean`.
  Each type replaces a loose `Prop` hypothesis that more than one Nitro
  statement repeated (`docs/lean/typed-library.md` rule 1).
-/
import ArmadaLean.Nitro.Constructions

namespace ArmadaLean.Nitro

variable {E : Type} [DecidableEq E]

/-! ## `TimedChannel`: a challenge duration that covers two round delays -/

/-- The fact `TimedChannel` wraps: `c`'s challenge duration covers two
    network delays of `ε`. Design decision 2026-10-31: `2 * ε` is
    sufficient for the Liveness proofs; the factor 2 comes from the round
    model, `docs/nitro-repair-2026-10-27.md:38-42`. `docs/lean/typed-library.md`
    §4, row `Channel.lean`. -/
def FixedPart.IsTimed (c : FixedPart) (ε : Time) : Prop := 2 * ε ≤ c.challengeDuration

instance (c : FixedPart) (ε : Time) : Decidable (c.IsTimed ε) :=
  inferInstanceAs (Decidable (2 * ε ≤ c.challengeDuration))

/-- A channel whose challenge duration covers two round delays of `ε`
    (`FixedPart.IsTimed`). `docs/lean/typed-library.md` §4, row
    `Channel.lean`. -/
def TimedChannel (ε : Time) : Type := {c : FixedPart // c.IsTimed ε}

namespace TimedChannel

variable {ε : Time}

/-- Coercion to the carrier (`writing-lean.md` §3, rule 2 of
    `typed-library.md`). -/
instance : CoeOut (TimedChannel ε) FixedPart := ⟨Subtype.val⟩

@[simp] theorem dur_le (c : TimedChannel ε) : 2 * ε ≤ (c : FixedPart).challengeDuration := c.property

/-- Decidable smart constructor (`typed-library.md` rule 2): `none` when
    `c`'s challenge duration is too short for `ε`. -/
def ofFixedPart? (c : FixedPart) (ε : Time) : Option (TimedChannel ε) :=
  if h : c.IsTimed ε then some ⟨c, h⟩ else none

@[simp] theorem ofFixedPart?_eq_some_iff {c : FixedPart} {ε : Time} {t : TimedChannel ε} :
    ofFixedPart? c ε = some t ↔ (t : FixedPart) = c := by
  unfold ofFixedPart?
  split
  · constructor
    · intro h; cases h; rfl
    · intro h; cases t with
      | mk tc htc => cases h; rfl
  · constructor
    · intro h; cases h
    · intro h; subst h; rename_i hcon; exact absurd t.property hcon

end TimedChannel

/-! ## `ConsensusMember`: `p` takes part in a channel that runs the consensus app -/

/-- `p` is a participant of `c`, and `c` runs the consensus app. The consensus round
    lemmas of `Liveness.lean` need the two facts together. -/
structure ConsensusMember (apps : Apps E) (p : Participant) (c : FixedPart) : Prop where
  app : apps c.appDef = consensusRules
  mem : p ∈ c.participants

/-- A `ConsensusMember` whose challenge duration covers two round delays of `ε`
    (`FixedPart.IsTimed`). The round lemmas that read a challenge deadline need it. -/
structure TimedConsensusMember (apps : Apps E) (p : Participant) (ε : Time) (c : FixedPart) :
    Prop extends ConsensusMember apps p c where
  timed : c.IsTimed ε

/-- Under the consensus app, a candidate that a support proof of `c` accepts is the one
    state of the proof, and every participant signed it. So when each state of the proof
    that `p` signed is a state of `sent`, the candidate is a state of `c` in `sent`. -/
theorem ConsensusMember.sent_cand {apps : Apps E} {p : Participant} {c : FixedPart}
    (hC : ConsensusMember apps p c) {sent : List (SignedState E)} {proof : SupportProof E}
    {cand : State E} (hU : ∀ ss ∈ proof, p ∈ ss.signers → ∃ x ∈ sent, x.state = ss.state)
    (hs : (apps c.appDef).supports c proof cand = true) :
    ∃ x ∈ sent, x.state = cand ∧ cand.channel = c := by
  rw [hC.app] at hs
  match proof, hs with
  | [ss], hs =>
    simp only [consensusRules, Bool.and_eq_true, decide_eq_true_eq] at hs
    obtain ⟨⟨hss, hch⟩, hall⟩ := hs
    obtain ⟨x, hx, hxs⟩ := hU ss (List.mem_singleton_self _) (hall p (hch ▸ hC.mem))
    exact ⟨x, hx, hxs.trans hss, hss ▸ hch⟩

/-! ## `LedgerChannel`: the channel's own `kind`, not the app it runs -/

/-
  Design decision 2026-10-31: being a ledger channel is the channel's own
  property, `c.kind = .ledger`, which the on-chain operations
  (`Adjudicator.deposit`/`transfer`/`reclaim`) already use. The consensus
  app is a separate fact about the channel's app, not part of "ledger".

  This splits the old `IsLedgerChannel apps c := c.kind = .ledger ∧ apps
  c.appDef = consensusRules` (`Constructions.lean`, now removed). The two
  conjuncts disagree on a reachable state (checked separately: `lake env lean` clean), with
  `apps1 := fun _ => noRules` (a `Rules` value that never supports
  anything) and `c0 : FixedPart := ⟨[], 0, ⟨0⟩, 2, .ledger⟩`. One `deposit`
  reaches a state `s1` where `c0` holds a real balance
  (`s1.balances.get c0.address = 1`) and `Reachable apps1 s1` holds. At
  `s1`, `c0.kind = .ledger` holds, but `apps1 c0.appDef = consensusRules`
  does not: `apps1` never maps `c0.appDef` to `consensusRules`. That
  finding is why `LedgerChannel` carries only `kind`: a type that also
  carried the app fact would hide, inside one name, two facts a reachable
  state can pull apart. `FixedPart.RunsConsensus` (`Constructions.lean`)
  is the separate, named premise a proof adds where it needs the app fact.
-/

/-- A channel that is, by its own `kind` field, a ledger channel (design
    decision 2026-10-31; see the note above). `docs/lean/typed-library.md`
    §4, row `Channel.lean`. -/
structure LedgerChannel where
  channel : FixedPart
  isLedger : channel.kind = .ledger

namespace LedgerChannel

/-- Coercion to the carrier (`writing-lean.md` §3, rule 2 of
    `typed-library.md`). -/
instance : CoeOut LedgerChannel FixedPart := ⟨LedgerChannel.channel⟩

@[simp] theorem kind_eq (c : LedgerChannel) : (c : FixedPart).kind = .ledger := c.isLedger

/-- Decidable smart constructor (`typed-library.md` rule 2): `kind = .ledger`
    is decidable (`ChannelKind` has `DecidableEq`), unlike the old
    `IsLedgerChannel`'s app conjunct. -/
def ofFixedPart? (c : FixedPart) : Option LedgerChannel :=
  if h : c.kind = .ledger then some ⟨c, h⟩ else none

@[simp] theorem ofFixedPart?_eq_some_iff {c : FixedPart} {t : LedgerChannel} :
    ofFixedPart? c = some t ↔ (t : FixedPart) = c := by
  unfold ofFixedPart?
  split
  · constructor
    · intro h; cases h; rfl
    · intro h; cases t with
      | mk tc htc => cases h; rfl
  · constructor
    · intro h; cases h
    · intro h; subst h; rename_i hcon; exact absurd t.isLedger hcon

end LedgerChannel

end ArmadaLean.Nitro
