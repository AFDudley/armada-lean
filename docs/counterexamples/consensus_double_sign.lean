/-
  Failure test: the honest signer's double-sign (Nitro-24, Nitro:653-658).

  Before the own-violation rule added on 2026-11-01, the honest
  `p0` could sign two consensus states of one channel at one turn above the
  funding point with two outcomes: `stA` pays `p0` 5, `stB` pays it 4. The
  adversary then challenges with `stB`, `p0` cannot answer at the same turn,
  and the outcome that is worse for `p0` finalizes. The setup rule of
  `HonestSend` covered only the turns below the funding point.

  Design decision 2026-11-01: own-violation is one rule for every
  participant. The honest signer commits no own-violation of kind (a)
  (`HonestSend.noConflict`, `OwnViolation.Conflict`): `stB` after `stA` is
  one (`doubleSign_conflict`), so the honest machine never sends it
  (`doubleSign_not_honest`).

  This file is not part of the `ArmadaLean` library. Check it with
  `lake env lean docs/counterexamples/consensus_double_sign.lean`.
-/
import ArmadaLean.Spec.Nitro.Liveness

namespace ArmadaLean.Nitro.CounterexampleDoubleSign

open ArmadaLean.Nitro

def q0 : Participant := ⟨0⟩
def p0 : Participant := ⟨1⟩

/-- A two-party channel above its funding point at turn 5. -/
def c0 : FixedPart :=
  { participants := [q0, p0], nonce := 0, appDef := ⟨0⟩, challengeDuration := 6, kind := .virtual }

def oA : Outcome Nat := .allocation [alloc (.external 0) 5, alloc (.external 1) 5]
def oB : Outcome Nat := .allocation [alloc (.external 0) 6, alloc (.external 1) 4]

/-- The two alternative states at turn 5. -/
def stA : State Nat :=
  { channel := c0, turnNum := 5, outcome := oA, isFinal := false, appData := .opaque 0 }
def stB : State Nat :=
  { channel := c0, turnNum := 5, outcome := oB, isFinal := false, appData := .opaque 0 }

/-- `stB` after `stA` is an own-violation of kind (a): one channel, one slot,
    two outcomes. -/
theorem doubleSign_conflict : OwnViolation.Conflict [⟨stA, [p0]⟩] stB :=
  ⟨⟨stA, [p0]⟩, List.mem_singleton_self _, rfl, rfl, by decide⟩

/-- Once `p0` signed `stA`, the honest machine never lets it sign `stB`. -/
theorem doubleSign_not_honest (apps : Apps Nat) (net : NetworkState Nat p0)
    (h : ⟨stA, [p0]⟩ ∈ net.sent) : ¬ (HonestMove.send stB).Feasible apps net := fun hf =>
  ((HonestMove.Feasible_send _ _ _).1 hf).noConflict
    ⟨_, List.mem_cons_of_mem _ h, rfl, rfl, by decide⟩

#print axioms doubleSign_conflict
#print axioms doubleSign_not_honest

end ArmadaLean.Nitro.CounterexampleDoubleSign
