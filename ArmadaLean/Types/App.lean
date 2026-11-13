/-
  Desirable apps (`Desirable`): individual rationality (IR), incentive
  compatibility (IC) and value conservation of an app at every state
  (`AppIR`, `AppIC`, `Conserving`).

  A desirable app is a compliant app that is incentive
  compatible and individually rational at every state, for every role. "IR
  at every state: from any state, an online honest participant can enforce
  at least what its holdings give it" (ForceMove:410-416, 125-130);
  "holdings: the signed states and vouchers a participant holds". Assets
  leave a channel only through a finalized outcome of that channel
  (`transfer_requires_finalized`), so "`p` takes its assets out" is "`p`
  can finalize an outcome of `c` that pays `p` at least its share"
  (`CanTakeOut`); the game itself need not end.

  `AppIR` asks this from every reachable state where `p` holds a share
  (`HoldsShare`). The channel must be open, at a turn record no higher than
  the held candidate: a reachable history can contain a stretch where `p`
  waited and let a challenge it should have answered run or expire, and no
  app can undo that.

  The papers assume desirable apps and never
  state the premise, as they assume participants that follow the protocol.
  The Nitro-24 statements (`finalizable_or_two_enabled`,
  `single_enabled_is_finalizable`, `Liveness.lean`) take `Desirable`
  (desirable apps are defined first, and
  independently of the theorems).

  "IC at every state: at no state does a participant gain by deviating from
  the rules or by aborting" (ForceMove:339-347, the
  Rock-Paper-Scissors example: "Without the added incentive of Bob being the
  default winner in this position, it could be in Alice's interest to end
  the game at this point, by refusing to reveal the outcome"). Each state
  carries a resolution, the outcome that finalizes if the game stops there.
  The mover of the next turn aborts when it signs no next state; the
  current state then finalizes. A move outside the rules is not supported,
  so it gives the mover nothing an abort does not give. `AppIC` asks: when
  the rules let the game go on from a supported non-final state, the next
  mover has a move by the rules (`RulesMove`) that pays it at least the
  current resolution. A final state ends the game, so a conclude move is not
  a move of the game.

  The proofs that the consensus app and the ForceMove apps whose game
  library takes nothing from a non-mover are IR are in
  `ArmadaLean/Nitro/TakeOut.lean` (`TakeOut.consensus_IR`,
  `TakeOut.forceMove_IR`). The IC proofs and the proof that the go-nitro
  payment rules (`PaymentRules`) give a desirable app are there too.
-/
import ArmadaLean.Nitro.Reachable
import ArmadaLean.Types.Channel

namespace ArmadaLean.Nitro

variable {E : Type} [DecidableEq E]

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
    condition applies at every state. go-nitro
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

/-- A move by the rules `r` from the supported state `cand` of `c`: a
    non-final state `cand'` of `c` at the next turn, with a support `proof'`
    whose states are states of `cand`'s support `proof` or new states with
    `cand'`. -/
def RulesMove (r : Rules E) (c : FixedPart) (proof : SupportProof E) (cand : State E)
    (proof' : SupportProof E) (cand' : State E) : Prop :=
  r.supports c proof' cand' = true ∧ cand'.channel = c ∧ cand'.turnNum = cand.turnNum + 1 ∧
    cand'.isFinal = false ∧ ∀ ss ∈ proof', ss ∈ proof ∨ ss.state = cand'

/-- IC at every state of the app `a`, for the destination map `dest`: at
    every supported non-final state of a channel of `a`, if the rules let
    the game go on, the mover `q` of the next turn has a move by the rules
    that pays `dest q` at least the current resolution. So `q` does not gain
    by aborting. -/
structure AppIC (apps : Apps E) (a : AppId) (dest : Participant → E) : Prop where
  noAbortGain : ∀ (c : FixedPart) (proof : SupportProof E) (cand : State E) (q : Participant),
    c.appDef = a → (apps a).supports c proof cand = true → cand.channel = c →
    cand.isFinal = false → ({ cand with turnNum := cand.turnNum + 1 } : State E).mover = some q →
    (∃ proof' cand', RulesMove (apps a) c proof cand proof' cand') →
    ∃ proof' cand', RulesMove (apps a) c proof cand proof' cand' ∧
      share cand.outcome (dest q) ≤ share cand'.outcome (dest q)

/-- One conserving step from the outcome `o` to `o'` with the mover `q`:
    the outcome stays, or the step is a go-nitro payment step
    (`SingleAssetPayments.sol`, `_requireValidOutcome` and
    `_requireValidTransition`). The destinations and the entry count stay
    ("Destinations may not change"), every entry is a simple allocation
    ("not a simple allocation"), each destination appears once (Nitro:744-746:
    "each address only appears once in the allocation"), the total stays
    ("Total allocated cannot change"), and an entry falls only when it is
    the mover's own entry and no other participant's ("Nonmover balance
    decreased"). -/
def ConservingStep (dest : Participant → E) (q : Participant) (o o' : Outcome E) : Prop :=
  o' = o ∨
  (o'.entries.map Entry.dest = o.entries.map Entry.dest ∧ (o.entries.map Entry.dest).Nodup ∧
    (∀ e ∈ o.entries ++ o'.entries, e.item.isGuarantee = false) ∧
    o'.entries.total = o.entries.total ∧
    ∀ (i : Nat) (e e' : Entry E), o.entries[i]? = some e → o'.entries[i]? = some e' →
      e'.amount < e.amount → e.dest = .external (dest q) ∧ ∀ r, e.dest = .external (dest r) → r = q)

/-- Value conservation of the app `a`, for the destination map `dest`
    (SATP §2.2 footnote 7: "Care must be taken
    to ensure application rules encode the fair distribution of assets";
    go-nitro `SingleAssetPayments.sol`). A transition of the app is a
    consecutive pair of states of a support proof (ForceMove:744-778: a
    support is a run of valid moves). Every such transition is a
    `ConservingStep` with the mover of the new state. A one-state support
    (the consensus app) holds no transition. -/
structure Conserving (apps : Apps E) (a : AppId) (dest : Participant → E) : Prop where
  conserve : ∀ (c : FixedPart) (proof : SupportProof E) (cand : State E), c.appDef = a →
    (apps a).supports c proof cand = true →
    ∀ (i : Nat) (m1 m2 : SignedState E) (q : Participant), proof[i]? = some m1 →
      proof[i + 1]? = some m2 → m2.state.mover = some q →
      ConservingStep dest q m1.state.outcome m2.state.outcome

/-- A desirable app: IR, IC and value conservation at every state, for the
    destination map `dest`. -/
structure Desirable (apps : Apps E) (a : AppId) (dest : Participant → E) : Prop where
  ir : AppIR apps a dest
  ic : AppIC apps a dest
  conserves : Conserving apps a dest

/-- A ForceMove game library with the go-nitro payment rules: a transition
    is valid exactly when the new state has a mover and the transition is a
    `ConservingStep` with that mover. -/
structure PaymentRules (vt : State E → State E → Bool) (dest : Participant → E) : Prop where
  valid_iff : ∀ s s', vt s s' = true ↔
    ∃ q, s'.mover = some q ∧ ConservingStep dest q s.outcome s'.outcome

end ArmadaLean.Nitro
