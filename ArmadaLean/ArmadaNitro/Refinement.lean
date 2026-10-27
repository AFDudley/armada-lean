/-
  Armada adjudicator: refinement of the Nitro specification. The abstraction
  is `toNitro` (State.lean): for each token, a channel's Nitro balance is the
  total value of its notes. Every Armada step maps to the corresponding Nitro
  step of the same token, or to no step. The map is exact up to
  `NitroEquiv`, which no Nitro operation can observe.

  Which Nitro theorems carry over, and how: `docs/armada-nitro-theorems.md`,
  section "Nitro theorems through the refinement". In short:
  * A Nitro theorem over `Nitro.Reachable` whose statement `NitroEquiv`
    preserves carries over by `nitro_invariant_carries`.
  * A Nitro theorem over one `Nitro.Step` carries over by
    `nitro_step_carries`.
  * A Nitro theorem about one `apply` result (`..._requires`, `..._effects`,
    `..._fails...`) carries over by `step_refines`.
  * A Nitro can-happen theorem does not carry over: the refinement is one-way.
    The status calls lift by `nitro_status_call_lifts`. Deposits and
    transfers have note-level can-happen theorems in `Liveness.lean`.

  Every theorem has proof `sorry`; the statements are the deliverable.
-/
import ArmadaLean.ArmadaNitro.Operations

namespace ArmadaLean.ArmadaNitro

set_option autoImplicit false

open ArmadaLean.Nitro (Participant FixedPart Apps Adjudicator)

variable {cfg : Config} {apps : Apps}

/-- The deployment is the Nitro genesis, up to `NitroEquiv`. -/
theorem toNitro_genesis (ps : PoolState) (t : Token) :
    NitroEquiv (toNitro (genesis ps) t) Nitro.Adjudicator.genesis := by
  sorry

/-- No Nitro operation can tell two `NitroEquiv` adjudicators apart: an
    operation succeeds on one exactly when it succeeds on the other, and the
    results are again `NitroEquiv`. -/
theorem nitroEquiv_apply {a b a' : Adjudicator} (h : NitroEquiv a b) (caller : Participant)
    (op : Nitro.Op) (ha : a.apply apps caller op = some a') :
    ∃ b', b.apply apps caller op = some b' ∧ NitroEquiv a' b' := by
  sorry

/-- **Refinement, one step.** An Armada step on token `t` is the Nitro
    operation `call.toNitro t` on the abstraction, with the result equal to the
    abstraction of the new state up to `NitroEquiv`. A pool step by another
    user, and a call on another token, change nothing that the Nitro copy of
    `t` can observe. -/
theorem step_refines {call : Call} {s s' : ArmadaState} (h : ArmadaStep cfg apps call s s')
    (t : Token) :
    (∃ op, call.toNitro t = some op ∧ ∃ caller n',
      (toNitro s t).apply apps caller op = some n' ∧ NitroEquiv n' (toNitro s' t)) ∨
    (call.toNitro t = none ∧ NitroEquiv (toNitro s t) (toNitro s' t)) := by
  sorry

/-- **Refinement, histories.** The abstraction of every reachable Armada state
    is a reachable Nitro state, up to `NitroEquiv`. -/
theorem toNitro_reachable {s : ArmadaState} (hs : ArmadaReachable cfg apps s) (t : Token) :
    ∃ n, Nitro.Reachable apps n ∧ NitroEquiv n (toNitro s t) := by
  sorry

/-- **Carry-over of a Nitro invariant.** A property `P` of Nitro adjudicators
    that `NitroEquiv` preserves and that holds on every reachable Nitro state
    holds on the abstraction of every reachable Armada state. -/
theorem nitro_invariant_carries (P : Adjudicator → Prop)
    (hP : ∀ a b, NitroEquiv a b → P a → P b)
    (hN : ∀ n, Nitro.Reachable apps n → P n) {s : ArmadaState}
    (hs : ArmadaReachable cfg apps s) (t : Token) : P (toNitro s t) := by
  sorry

/-- **Carry-over of a Nitro step property.** A relation `R` that `NitroEquiv`
    preserves on both sides, and that holds across every Nitro step from a
    reachable state, holds across every Armada step from a reachable state,
    or the step changes nothing that the Nitro copy of `t` observes. -/
theorem nitro_step_carries (R : Adjudicator → Adjudicator → Prop)
    (hR : ∀ a a' b b', NitroEquiv a b → NitroEquiv a' b' → R a a' → R b b')
    (hN : ∀ n n', Nitro.Reachable apps n → Nitro.Step apps n n' → R n n')
    {call : Call} {s s' : ArmadaState} (hs : ArmadaReachable cfg apps s)
    (h : ArmadaStep cfg apps call s s') (t : Token) :
    R (toNitro s t) (toNitro s' t) ∨ NitroEquiv (toNitro s t) (toNitro s' t) := by
  sorry

/-- **The status calls lift.** A Nitro reclaim, challenge, checkpoint or
    conclude that succeeds on the abstraction is an Armada step, and so is a
    tick. These calls spend no note, so the pool adds no condition. -/
theorem nitro_status_call_lifts (s : ArmadaState) (t : Token) (call : Call)
    (hcall : (∃ l v, call = .reclaim t l v) ∨
      (∃ p c proof candidate, call = .challenge t p c proof candidate) ∨
      (∃ c proof candidate, call = .checkpoint t c proof candidate) ∨
      (∃ c ss, call = .conclude t c ss) ∨ (∃ dt, call = .tick dt))
    (op : Nitro.Op) (hop : call.toNitro t = some op) (caller : Participant)
    (hcaller : ∀ p, call.challenger = some p → caller = p) (n : Adjudicator)
    (hn : (toNitro s t).apply apps caller op = some n) :
    ∃ s', ArmadaStep cfg apps call s s' ∧ NitroEquiv n (toNitro s' t) ∧ s'.pool = s.pool := by
  sorry

end ArmadaLean.ArmadaNitro
