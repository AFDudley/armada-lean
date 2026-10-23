/-
  ArmadaLean.Adjudicator — the armada-nitro adjudicator model, phase 1
  stage A (state, operations, the three assumptions, theorem statements).

  Read in this order:
  - `Outcome.lean`      — allocations, guarantees, the priority payout rule.
  - `Assumptions.lean`  — hash and signature axioms (assumptions 1, 2).
  - `Channel.lean`      — channel state, support, modes, finalizability.
  - `Notes.lean`        — the Armada layer: pool notes, the owned-spend
                           circuit, proof soundness (assumption 3).
  - `State.lean`        — the full adjudicator state and `heldValue`.
  - `Operations.lean`   — every call and its effect.
  - `Reachability.lean` — every state any sequence of calls can reach.
  - `Safety.lean`       — the theorem statements, proofs `sorry`.

  See `Safety.lean`'s module comment for the three questions this model
  answers and the sources it answers them from.
-/
import ArmadaLean.Adjudicator.Outcome
import ArmadaLean.Adjudicator.Assumptions
import ArmadaLean.Adjudicator.Channel
import ArmadaLean.Adjudicator.Notes
import ArmadaLean.Adjudicator.State
import ArmadaLean.Adjudicator.Operations
import ArmadaLean.Adjudicator.Reachability
import ArmadaLean.Adjudicator.Safety
