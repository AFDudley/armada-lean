/-
  The round clock freeze, and the rule that removes it (added
  2026-11-01: nobody can stop the clock; time advancing is an assumption of
  the model, not a move).

  `Threat.Round` (Strategy.lean) bounds a round by `net'.chain.now <
  net.chain.now + T.ε` (Nitro:535-537, "before time t + ε"). Time is a natural
  number. With `ε = 1` the bound leaves no room for a tick: every round ends at
  the clock where it starts (`freeze`). Then `p` stops the clock by playing
  `.wait 0` forever, no challenge ever expires, and `p` prevents every outcome
  that needs an expiry. Example: the maximal `SupportWindow` app, with `p`
  holding a support up to turn 5 and the adversary a support at turn 6. Then
  `p` has no finalizable outcome and no enabled outcome, so
  `finalizable_or_two_enabled` fails. With `ε ≥ 2`, every outcome that the
  adversary can challenge at turn 6 is enabled, and the claim holds for that
  instance.

  The rule: `Capable.clockRuns : 2 ≤ T.ε`, which `Assumptions` carries. With
  `Capable.capableTick`, the adversary can then always tick in a round
  (`clock_runs`). `p` can always move the clock itself
  (`UnbeatableIn.clock_advances`, Strategy.lean). So no party stops the
  clock. A threat with `ε = 1` is not capable (`not_capable`). The Turbo game
  (`Threat.TransfersOnly`, `Bounds` only) is timeless by Nitro:779-781 and
  does not carry `Capable`, so the rule does not touch it.

  This file is not part of the `ArmadaLean` library. Check it with
  `lake env lean docs/counterexamples/round_clock_freeze.lean`.
-/
import ArmadaLean.Spec.Nitro.Liveness

namespace ArmadaLean.Nitro.ClockFreeze

open ArmadaLean.Nitro

variable {E : Type} [DecidableEq E]

/-- With `ε = 1`, a round of `.wait 0` ends at the clock where it starts. -/
theorem freeze (apps : Apps E) {p : Participant} (T : Threat E p) (hε : T.ε = 1)
    {n n' : NetworkState E p} (h : T.Round apps (.wait 0) n n') :
    (n'.applyHonest (.wait 0)).chain.now = n.chain.now := by
  obtain ⟨hseq, hlt⟩ := h
  have hle := hseq.now_le
  rw [hε] at hlt
  show n'.chain.now + 0 = n.chain.now
  exact le_antisymm (Nat.lt_succ_iff.mp hlt) hle

omit [DecidableEq E] in
/-- A threat with `ε = 1` is not capable: `Capable.clockRuns` fails. -/
theorem not_capable (apps : Apps E) {p : Participant} (T : Threat E p) (hε : T.ε = 1) :
    ¬ Capable apps p T := fun h => by
  have := h.clockRuns
  rw [hε] at this
  exact absurd this (by decide)

/-- A sub-round of pure adversary play appended after a round. -/
theorem trans_nil {apps : Apps E} {p : Participant} {T : Threat E p} {t : Time}
    {pending : List (Op E)} {net mid net' : NetworkState E p}
    (h1 : Threat.RoundSeq apps T t pending net mid) (h2 : Threat.RoundSeq apps T t [] mid net') :
    Threat.RoundSeq apps T t pending net net' := by
  induction h1 with
  | nil => exact h2
  | land hsplit _ ih => exact .land hsplit (ih h2)
  | tick hfeas hgate _ ih => exact .tick hfeas hgate (ih h2)
  | other hfeas hnotick hnoland _ ih => exact .other hfeas hnotick hnoland (ih h2)

/-- Under `Capable`, every move of `p` has a round in which the clock
    advances: the adversary ticks by 1 after `p`'s calls land. -/
theorem clock_runs (apps : Apps E) {p : Participant} (T : Threat E p) (hC : Capable apps p T)
    {m : HonestMove E} {n : NetworkState E p} (hfeas : m.Feasible apps n) :
    ∃ n', T.Round apps m n n' ∧ n.chain.now < n'.chain.now := by
  have hnotick : ∀ op ∈ m.calls, ∀ dt, op ≠ Op.tick dt := by
    cases m with
    | react r => exact fun op hop => Op.HonestFeasible.not_tick (hfeas.1 op hop)
    | wait _ => intro op hop; simp [HonestMove.calls] at hop
  obtain ⟨n1, hseq, hnow⟩ := Threat.RoundSeq.landAll apps T n.chain.now m.calls hnotick n
  refine ⟨n1.applyAdv apps (.tick 1), ⟨trans_nil hseq (.tick (hC.capableTick _ _) (Or.inl rfl) .nil), ?_⟩, ?_⟩
  · show n1.chain.now + 1 < n.chain.now + T.ε
    rw [hnow]
    exact Nat.add_lt_add_left (lt_of_lt_of_le Nat.one_lt_two hC.clockRuns) _
  · show n.chain.now < n1.chain.now + 1
    rw [hnow]
    exact Nat.lt_succ_self _

end ArmadaLean.Nitro.ClockFreeze
