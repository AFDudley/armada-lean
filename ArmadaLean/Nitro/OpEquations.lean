/-
  The operation equations: repair pass step R.2 (armada-laconic `docs/process.md`, "The
  repair pass"). One equation per `Op` constructor states `Adjudicator.apply` in the
  dependent-`if` form: `if h : Pre then some (Effect ⟨_, h⟩) else none`. The preconditions
  and the effects are in `Adjudicator.lean`, section "One precondition and one effect per
  operation". The statements are in `ArmadaLean/Spec/Nitro/OpEquations.lean`.

  The names end in `_equation`, because the helpers `Adjudicator.apply_<op>` of
  `Lemmas.lean` (`apply` of an `Op` is the old operation, by `rfl`) hold the shorter names.

  A failed call stays in the model: the adversary may submit any call, and go-nitro reverts
  it (`none`).

  The go-nitro line numbers are those of the go-nitro contracts as armada-nitro vendored them
  unmodified, armada-nitro commit `8edacc10`, `src/nitro/`.
-/
import ArmadaLean.Nitro.Lemmas

namespace ArmadaLean.Nitro

variable {E : Type} [DecidableEq E]

namespace Adjudicator

/-- The `deposit` equation. go-nitro MultiAssetHolder.sol:38-64 `deposit`. -/
theorem apply_deposit_equation (apps : Apps E) (caller : Participant) (a : Address E)
    (expectedHeld x : Coins) (s : Adjudicator E) :
    s.apply apps caller (.deposit a expectedHeld x) =
      if h : s.DepositPre a expectedHeld then some (s.depositEffect expectedHeld ⟨a, h⟩ x)
      else none := by
  sorry

/-- The `transfer` equation. go-nitro MultiAssetHolder.sol:75-110 `transfer`. -/
theorem apply_transfer_equation (apps : Apps E) (caller : Participant) (a : FixedPart)
    (b : Address E) (s : Adjudicator E) :
    s.apply apps caller (.transfer a b) =
      if h : s.TransferPre a b then some (s.transferEffect b ⟨a, h⟩) else none := by
  sorry

/-- The `reclaim` equation. go-nitro MultiAssetHolder.sol:234-256 `reclaim`. -/
theorem apply_reclaim_equation (apps : Apps E) (caller : Participant) (l v : FixedPart)
    (s : Adjudicator E) :
    s.apply apps caller (.reclaim l v) =
      if h : s.ReclaimPre l v then some (s.reclaimEffect v ⟨l, h⟩) else none := by
  sorry

/-- The `challenge` equation. go-nitro ForceMove.sol:39-81 `challenge`. -/
theorem apply_challenge_equation (apps : Apps E) (caller : Participant) (c : FixedPart)
    (proof : SupportProof E) (candidate : State E) (s : Adjudicator E) :
    s.apply apps caller (.challenge c proof candidate) =
      if h : s.ChallengePre apps caller c proof candidate then
        some (s.challengeEffect apps caller c proof ⟨candidate, h⟩)
      else none := by
  sorry

/-- The `checkpoint` equation. go-nitro ForceMove.sol:90-119 `checkpoint`. -/
theorem apply_checkpoint_equation (apps : Apps E) (caller : Participant) (c : FixedPart)
    (proof : SupportProof E) (candidate : State E) (s : Adjudicator E) :
    s.apply apps caller (.checkpoint c proof candidate) =
      if h : s.CheckpointPre apps c proof candidate then
        some (s.checkpointEffect apps c proof ⟨candidate, h⟩)
      else none := by
  sorry

/-- The `conclude` equation. go-nitro ForceMove.sol:127-132 `conclude` and
    ForceMove.sol:140-170 `_conclude`. -/
theorem apply_conclude_equation (apps : Apps E) (caller : Participant) (c : FixedPart)
    (ss : SignedState E) (s : Adjudicator E) :
    s.apply apps caller (.conclude c ss) =
      if h : s.ConcludePre c ss then some (s.concludeEffect c ⟨ss, h⟩) else none := by
  sorry

/-- The `tick` equation. go-nitro StatusManager.sol:17-30 `_mode` reads `block.timestamp`;
    the clock always moves. -/
theorem apply_tick_equation (apps : Apps E) (caller : Participant) (dt : Time)
    (s : Adjudicator E) :
    s.apply apps caller (.tick dt) =
      if h : s.TickPre dt then some (s.tickEffect ⟨dt, h⟩) else none := by
  rw [dif_pos (show s.TickPre dt from Nat.le_add_right s.now dt)]
  rfl

end Adjudicator

end ArmadaLean.Nitro
