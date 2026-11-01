/-
  Individual rationality (IR) of an app at every state, as one type
  (`AppIR`).

  armada-laconic `labbook/2026-10-30-app-classes-ic-ir.md` §2 (operator,
  2026-10-30): a desirable app is a compliant app that is incentive
  compatible and individually rational at every state, for every role. "IR
  at every state: from any state, an online honest participant can enforce
  at least what its holdings give it" (ForceMove:410-416, 125-130);
  "holdings: the signed states and vouchers a participant holds". Assets
  leave a channel only through a finalized outcome of that channel
  (`transfer_requires_finalized`), so "`p` takes its assets out" is "`p`
  can finalize an outcome of `c` that pays `p` at least its share"
  (`CanTakeOut`); the game itself need not end (labbook §11, operator
  correction of 2026-11-01).

  `AppIR` asks this from every reachable state where `p` holds a share
  (`HoldsShare`). The channel must be open, at a turn record no higher than
  the held candidate: a reachable history can contain a stretch where `p`
  waited and let a challenge it should have answered run or expire, and no
  app can undo that.

  Operator ruling 2026-11-01: the papers assume desirable apps and never
  state the premise, as they assume participants that follow the protocol.
  The Nitro-24 statements (`finalizable_or_two_enabled`,
  `single_enabled_is_finalizable`, `Liveness.lean`) take `AppIR`.

  The proofs that the consensus app and the ForceMove apps whose game
  library takes nothing from a non-mover are IR are in
  `ArmadaLean/Nitro/TakeOut.lean` (`TakeOut.consensus_IR`,
  `TakeOut.forceMove_IR`).
-/
import ArmadaLean.Nitro.Reachable
import ArmadaLean.Types.Channel

namespace ArmadaLean.Nitro

variable {E : Type} [DecidableEq E]

/-- The amount that an outcome pays the external destination `d`: the first
    entry for `d` (`Allocation.owed`). -/
def share (Ω : Outcome E) (d : E) : Coins := Ω.entries.owed (.external d)

/-- The facts about the states `p` signed that `HoldsShare` gives: every
    state of `c` is at most at turn `Th`, and pays `d` at least `x` when it is
    in the window of `Th` or final. -/
def SentBelow (sent : List (SignedState E)) (c : FixedPart) (d : E) (x Th : Nat) : Prop :=
  ∀ s ∈ sent, s.state.channel = c → s.state.turnNum ≤ Th ∧
    ((Th < s.state.turnNum + c.n ∨ s.state.isFinal = true) → x ≤ share s.state.outcome d)

/-- What `p`'s holdings give it at the destination `d`: at least `x`, the
    payment of a supported candidate of `c` that `p` holds. Every state of `c`
    that `p` signed is at most at the candidate's turn, and pays `d` at least
    `x` when it is in the candidate's window or final (`SentBelow`): the later
    and alternative moves of `p` are part of what its holdings give it. The
    channel is open, at a turn record no higher than the candidate's: `p` was
    online, so no challenge it should have answered is running. -/
def HoldsShare {p : Participant} (apps : Apps E) (net : NetworkState E p) (c : FixedPart) (d : E)
    (x : Coins) : Prop :=
  ∃ proof cand, (∀ ss ∈ proof, net.Holds ss) ∧ (apps c.appDef).supports c proof cand = true ∧
    cand.channel = c ∧ x ≤ share cand.outcome d ∧ SentBelow net.sent c d x cand.turnNum ∧
    ∃ t, net.chain.statusOf c = .open t ∧ t ≤ cand.turnNum

/-- `p` can take out `x` at `d`: it has an unbeatable strategy that finalizes
    `c` with an outcome that pays `d` at least `x`. -/
def CanTakeOut {p : Participant} (apps : Apps E) (T : Threat E p) (c : FixedPart) (d : E)
    (x : Coins) (net : NetworkState E p) : Prop :=
  Unbeatable apps T (fun n => ∃ Ω, n.Finalized c Ω ∧ x ≤ share Ω d) net

/-- A sufficient condition on a ForceMove game library: no valid transition
    reduces the payment to a participant that does not move. The candidate
    condition of the labbook §11 (operator, 2026-11-01). go-nitro
    `SingleAssetPayments.sol` has this rule ("for all non-movers the balance
    hasn't decreased"). -/
def NoTakeFromNonMover (vt : State E → State E → Bool) (dest : Participant → E) : Prop :=
  ∀ s s', vt s s' = true → ∀ q, s'.mover ≠ some q → share s.outcome (dest q) ≤ share s'.outcome (dest q)

/-- IR at every state of the app `a`, for the destination map `dest`: from
    every reachable state, every participant `p` can take out what its
    holdings give it at `dest p`. A structure, so that a statement that
    takes it takes one refined type (`docs/lean/typed-library.md` rule 1). -/
structure AppIR (apps : Apps E) (a : AppId) (dest : Participant → E) : Prop where
  takeOut : ∀ {p : Participant} (T : Threat E p), Assumptions apps p T →
    ∀ (net : Nitro.ReachableParticipant apps T) (c : TimedChannel T.ε) (x : Coins),
      (c : FixedPart).appDef = a → p ∈ (c : FixedPart).participants →
      HoldsShare apps net.state c (dest p) x → CanTakeOut apps T c (dest p) x net.state

end ArmadaLean.Nitro
