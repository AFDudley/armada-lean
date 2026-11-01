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
import Mathlib.Tactic.Says

namespace ArmadaLean.Nitro

variable {E : Type} [DecidableEq E]

namespace Adjudicator

/-- The `deposit` equation. go-nitro MultiAssetHolder.sol:38-64 `deposit`. -/
theorem apply_deposit_equation (apps : Apps E) (caller : Participant) (a : Address E)
    (expectedHeld x : Coins) (s : Adjudicator E) :
    s.apply apps caller (.deposit a expectedHeld x) =
      if h : s.DepositPre a expectedHeld then some (s.depositEffect expectedHeld ⟨a, h⟩ x)
      else none := by
  by_cases h : s.DepositPre a expectedHeld
  · rw [dif_pos h]
    have ⟨h1, h2, h3⟩ := h
    cases a with
    | external e => (simp? [Address.isExternal] at h1 says simp only [Address.isExternal, Bool.true_eq_false] at h1)
    | channel c =>
      simp only [Address.fundable, decide_eq_true_eq] at h2
      (simp? [apply, deposit, depositEffect, h2, h3] says simp only [apply, deposit, h2, h3, and_self, ↓reduceIte, depositEffect])
  · rw [dif_neg h]
    cases a with
    | external e => rfl
    | channel c =>
      simp only [apply, deposit]
      rw [if_neg]
      rintro ⟨h2, h3⟩
      exact h ⟨rfl, by (simp? [Address.fundable, h2] says simp only [Address.fundable, h2, decide_true]), h3⟩

/-- The `transfer` equation. go-nitro MultiAssetHolder.sol:75-110 `transfer`. -/
theorem apply_transfer_equation (apps : Apps E) (caller : Participant) (a : FixedPart)
    (b : Address E) (s : Adjudicator E) :
    s.apply apps caller (.transfer a b) =
      if h : s.TransferPre a b then some (s.transferEffect b ⟨a, h⟩) else none := by
  by_cases h : s.TransferPre a b
  · rw [dif_pos h]
    have ⟨hk, hb, hs⟩ := h
    obtain ⟨o, hso⟩ := Option.isSome_iff_exists.1 hs
    have hget : (s.transferSource? a b).get hs = o := by (simp? [hso] says simp only [hso, Option.get_some])
    simp only [apply, transfer, transferEffect, if_pos (And.intro hk hb), hget]
    unfold transferSource? at hso
    split at hso
    · split at hso
      · cases hso
        (simp? says simp only [FixedPart.address_eq, payTo_balances, setStatus_balances, payTo_held, setStatus_held, payTo_status, payTo_now, setStatus_now])
      · (simp? at hso says simp only [reduceCtorEq] at hso)
    · (simp? at hso says simp only [reduceCtorEq] at hso)
  · rw [dif_neg h]
    simp only [apply, transfer]
    split_ifs with hk
    · unfold TransferPre transferSource? at h
      split
      · split
        · (simp_all? says simp_all only [FixedPart.address_eq, finalOutcome_channel, true_and, Bool.not_eq_true, Option.isSome_eq_false_iff, Option.isNone_iff_eq_none, payTo_balances, setStatus_balances, payTo_held, setStatus_held, payTo_status, payTo_now, setStatus_now, reduceCtorEq])
        · rfl
      · rfl
    · rfl

/-- The `reclaim` equation. go-nitro MultiAssetHolder.sol:234-256 `reclaim`. -/
theorem apply_reclaim_equation (apps : Apps E) (caller : Participant) (l v : FixedPart)
    (s : Adjudicator E) :
    s.apply apps caller (.reclaim l v) =
      if h : s.ReclaimPre l v then some (s.reclaimEffect v ⟨l, h⟩) else none := by
  by_cases h : s.ReclaimPre l v
  · rw [dif_pos h]
    have ⟨hk, hv, hs⟩ := h
    obtain ⟨r, hso⟩ := Option.isSome_iff_exists.1 hs
    have hget : (s.reclaimSource? l v).get hs = r := by (simp? [hso] says simp only [hso, Option.get_some])
    simp only [apply, reclaim, reclaimEffect, if_pos (And.intro hk hv), hget]
    unfold reclaimSource? at hso
    split at hso
    · split at hso
      · split_ifs at hso with hc
        cases hso
        rw [if_pos hc]
      · (simp? at hso says simp only [reduceCtorEq] at hso)
    · (simp? at hso says simp only [reduceCtorEq] at hso)
  · rw [dif_neg h]
    simp only [apply, reclaim]
    split_ifs with hk
    · unfold ReclaimPre reclaimSource? at h
      split
      · split
        · split_ifs <;> simp_all
        · rfl
      · rfl
    · rfl

/-- The `challenge` equation. go-nitro ForceMove.sol:39-81 `challenge`. -/
theorem apply_challenge_equation (apps : Apps E) (caller : Participant) (c : FixedPart)
    (proof : SupportProof E) (candidate : State E) (s : Adjudicator E) :
    s.apply apps caller (.challenge c proof candidate) =
      if h : s.ChallengePre apps caller c proof candidate then
        some (s.challengeEffect apps caller c proof ⟨candidate, h⟩)
      else none := by
  by_cases h : s.ChallengePre apps caller c proof candidate
  · rw [dif_pos h]
    exact if_pos h
  · rw [dif_neg h]
    exact if_neg h

/-- The `checkpoint` equation. go-nitro ForceMove.sol:90-119 `checkpoint`. -/
theorem apply_checkpoint_equation (apps : Apps E) (caller : Participant) (c : FixedPart)
    (proof : SupportProof E) (candidate : State E) (s : Adjudicator E) :
    s.apply apps caller (.checkpoint c proof candidate) =
      if h : s.CheckpointPre apps c proof candidate then
        some (s.checkpointEffect apps c proof ⟨candidate, h⟩)
      else none := by
  by_cases h : s.CheckpointPre apps c proof candidate
  · rw [dif_pos h]
    exact if_pos h
  · rw [dif_neg h]
    exact if_neg h

/-- The `conclude` equation. go-nitro ForceMove.sol:127-132 `conclude` and
    ForceMove.sol:140-170 `_conclude`. -/
theorem apply_conclude_equation (apps : Apps E) (caller : Participant) (c : FixedPart)
    (ss : SignedState E) (s : Adjudicator E) :
    s.apply apps caller (.conclude c ss) =
      if h : s.ConcludePre c ss then some (s.concludeEffect c ⟨ss, h⟩) else none := by
  by_cases h : s.ConcludePre c ss
  · rw [dif_pos h]
    exact if_pos h
  · rw [dif_neg h]
    exact if_neg h

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
