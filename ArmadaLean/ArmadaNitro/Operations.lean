/-
  Armada adjudicator: the calls and the step relation. See `Notes.lean` for
  the design summary and `docs/armada-nitro-theorems.md` for the theorem map.

  The call set is the Nitro operation set (Nitro `Adjudicator.lean`: deposit,
  transfer, reclaim, challenge, checkpoint, conclude, tick), one call per
  token, plus `env`, a pool step by another pool user. There is no separate
  merge call and no batch call (operator ruling 2026-10-27, 1 and 3). A batch
  is a sequence of calls; `ArmadaReachable` covers every sequence.

  A call label holds what a caller submits: the token, the channel, and the
  notes that the call spends. A pool proof names the nullifiers of the notes
  it spends, so the spent notes belong to the submitted call. The keys of the
  created notes are chosen by the pool and are witnesses of the step.

  The status calls (reclaim, challenge, checkpoint, conclude) run the Nitro
  function on the abstraction `toNitro s t` and write back the one status that
  the Nitro function changed. They spend no note: a Nitro reclaim moves no
  coins (Adjudicator.lean:178-181).
-/
import ArmadaLean.ArmadaNitro.State

namespace ArmadaLean.ArmadaNitro

set_option autoImplicit false

open ArmadaLean.Nitro (Coins Time Participant FixedPart Address Outcome Allocation Entry Item
  ChannelStatus Apps Adjudicator SignedState SupportProof)

/-- A call to the Armada system.
    * `env`: a pool step by another pool user.
    * `deposit t c expectedHeld x fund merged`: go-nitro `deposit`
      (MultiAssetHolder.sol:38-63) of `x` into channel `c`, with the
      compare-and-swap value `expectedHeld` (ruling 5). The depositor's notes
      `fund` pay for a deposit note; the call merges the deposit note with the
      channel notes `merged` into one channel note (ruling 3).
    * `transfer t c b ins`: go-nitro `transfer` (MultiAssetHolder.sol:72-100)
      of channel `c`'s entry for `b`, paid from the channel notes `ins`.
    * `reclaim`, `challenge`, `checkpoint`, `conclude`: the Nitro operations of
      the same names, for token `t`.
    * `tick dt`: the chain clock moves. -/
inductive Call
  | env
  | deposit (t : Token) (c : FixedPart) (expectedHeld x : Coins) (fund merged : List Note)
  | transfer (t : Token) (c : FixedPart) (b : Address) (ins : List Note)
  | reclaim (t : Token) (l v : FixedPart)
  | challenge (t : Token) (challenger : Participant) (c : FixedPart) (proof : SupportProof)
      (candidate : Nitro.State)
  | checkpoint (t : Token) (c : FixedPart) (proof : SupportProof) (candidate : Nitro.State)
  | conclude (t : Token) (c : FixedPart) (ss : SignedState)
  | tick (dt : Time)

/-- The Nitro operation that a call is, for the Nitro copy of token `t`. A
    call on another token, and a pool step, are no operation of that copy. The
    clock is shared, so `tick` is an operation of every copy. -/
def Call.toNitro (t : Token) : Call → Option Nitro.Op
  | .env => none
  | .deposit t' c e x _ _ => if t' = t then some (.deposit c.address e x) else none
  | .transfer t' c b _ => if t' = t then some (.transfer c b) else none
  | .reclaim t' l v => if t' = t then some (.reclaim l v) else none
  | .challenge t' _ c proof candidate =>
    if t' = t then some (.challenge c proof candidate) else none
  | .checkpoint t' c proof candidate =>
    if t' = t then some (.checkpoint c proof candidate) else none
  | .conclude t' c ss => if t' = t then some (.conclude c ss) else none
  | .tick dt => some (.tick dt)

/-- The signed states a call submits (Nitro `Op.proofStates`). -/
def Call.proofStates : Call → SupportProof
  | .challenge _ _ _ proof _ => proof
  | .checkpoint _ _ proof _ => proof
  | .conclude _ _ ss => [ss]
  | _ => []

/-- The challenger of a challenge call. go-nitro
    `_requireChallengerIsParticipant` (ForceMove.sol:178-190) reads it. No
    other call reads its caller (Nitro:312-313). -/
def Call.challenger : Call → Option Participant
  | .challenge _ p _ _ _ => some p
  | _ => none

/-- The note key rule for a payout to `b` (ruling 4): a participant is paid at
    its payee key; a channel is credited with a note keyed to the
    adjudicator. -/
def PayKey (cfg : Config) : Address → CommitmentPreimage → Prop
  | .participant p, pre => pre.npk = cfg.payeeKey p
  | .channel _, pre => OwnedBy cfg.self pre

/-- Credit the payout note `e` to destination `b` in token `t`: a payment
    record for a participant, a new channel note for a channel (ruling 4). -/
def ArmadaState.credit (s : ArmadaState) (t : Token) (b : Address) (e : Note) : ArmadaState :=
  match b with
  | .participant p => s.pay t p e
  | .channel d => s.setChan t d { s.chanOf t d with notes := (s.chanOf t d).notes ++ [e] }

/-- Write back the status of channel `c` from the Nitro adjudicator `n`. -/
def ArmadaState.withNitroStatus (s : ArmadaState) (t : Token) (c : FixedPart) (n : Adjudicator) :
    ArmadaState :=
  s.setChan t c { s.chanOf t c with status := n.statusOf c }

/-- The amount that a transfer of `c`'s entry for `b` pays: go-nitro's
    affordable amount (MultiAssetHolder.sol:66, 162-191; Nitro
    `Allocation.paidTo`) at the channel's note total. -/
def ArmadaState.payout (s : ArmadaState) (t : Token) (c : FixedPart) (o : Allocation)
    (b : Address) : Coins :=
  o.paidTo (s.balance t c) b

/-- One successful step of the Armada system, labelled by its call. -/
inductive ArmadaStep (cfg : Config) (apps : Apps) : Call → ArmadaState → ArmadaState → Prop
  /-- Another pool user acts in the pool. The adjudicator's record does not
      change. -/
  | env {s : ArmadaState} (ps' : PoolState) (h : OtherUserStep cfg.self s.pool ps') :
      ArmadaStep cfg apps .env s { s with pool := ps' }
  /-- Deposit (go-nitro MultiAssetHolder.sol:38-63; Nitro:165-168). The channel
      is not finalized (ruling 3; Hydra `s-inc` is Open to Open,
      `Solvency.lagda.typ`:243-246). The channel's balance equals
      `expectedHeld` (ruling 5). Leg 1 is the depositor's pool step: it spends
      the depositor's notes `fund` (none keyed to the adjudicator) and creates
      the deposit note `d` of value `x`, keyed to the adjudicator. The
      depositor's proof names the adjudicator as its adapt contract and the
      channel in its adapt parameters, so only this call can execute it, for
      this channel (`spend_bound_to_adapt`, PoolSafety.lean:1842). Leg 2 is
      the adjudicator's owned spend: it merges the channel notes `merged` and
      `d` into the one channel note `new`. -/
  | deposit {s : ArmadaState} (t : Token) (c : FixedPart) (expectedHeld x : Coins)
      (fund merged keep others : List Note) (ps1 ps2 : PoolState) (d new : Note)
      (hOpen : (s.chanOf t c).status.IsOpen s.now)
      (hHeld : s.balance t c = expectedHeld)
      (hMerged : (s.chanOf t c).notes.Perm (merged ++ keep))
      (hFund : ∀ e ∈ fund, ¬ OwnedBy cfg.self e.2)
      (hLeg1 : PoolCall s.pool ps1 t fund (d :: others))
      (hd : OwnedBy cfg.self d.2 ∧ d.2.value = x)
      (hLeg2 : PoolCall ps1 ps2 t (merged ++ [d]) [new])
      (hNew : OwnedBy cfg.self new.2) :
      ArmadaStep cfg apps (.deposit t c expectedHeld x fund merged) s
        ({ s with pool := ps2 }.setChan t c { s.chanOf t c with notes := keep ++ [new] })
  /-- Transfer of an entry that the channel affords nothing (Nitro
      `transfer_zero_moves_nothing`). The call spends no note, so it cannot
      make another caller's pending payout stale. -/
  | transferZero {s : ArmadaState} (t : Token) (c : FixedPart) (b : Address) (o : Allocation)
      (hFin : (s.chanOf t c).status.finalOutcome s.now = some (.allocation o))
      (hEntry : ∃ amt, o.find b = some ⟨b, .alloc amt⟩)
      (hZero : s.payout t c o b = 0) :
      ArmadaStep cfg apps (.transfer t c b []) s
        (s.setChan t c { s.chanOf t c with
          status := (s.chanOf t c).status.withOutcome (.allocation (o.reduceOwed b 0)) })
  /-- Transfer (go-nitro MultiAssetHolder.sol:72-100; Nitro:765-772). The
      channel is finalized with an allocation that has an allocation entry for
      `b` (ruling 3). The call pays the affordable amount `x > 0`. It spends
      only the channel notes `ins`. It creates the payout note `pay` of value
      `x` with the note key of `b` (ruling 4) and the change note `change`,
      the one note that goes back to the channel (ruling 3). -/
  | transfer {s : ArmadaState} (t : Token) (c : FixedPart) (b : Address) (o : Allocation)
      (ins keep : List Note) (ps' : PoolState) (pay change : Note)
      (hFin : (s.chanOf t c).status.finalOutcome s.now = some (.allocation o))
      (hEntry : ∃ amt, o.find b = some ⟨b, .alloc amt⟩)
      (hPos : 0 < s.payout t c o b)
      (hIns : (s.chanOf t c).notes.Perm (ins ++ keep))
      (hCall : PoolCall s.pool ps' t ins [pay, change])
      (hPay : pay.2.value = s.payout t c o b ∧ PayKey cfg b pay.2)
      (hChange : OwnedBy cfg.self change.2) :
      ArmadaStep cfg apps (.transfer t c b ins) s
        (({ s with pool := ps' }.setChan t c
            { status := (s.chanOf t c).status.withOutcome
                (.allocation (o.reduceOwed b (s.payout t c o b))),
              notes := keep ++ [change] }).credit t b pay)
  /-- Nitro `Adjudicator.reclaim` (SATP Listing 2; go-nitro `reclaim`). -/
  | reclaim {s : ArmadaState} (t : Token) (l v : FixedPart) (n : Adjudicator)
      (h : (toNitro s t).reclaim l v = some n) :
      ArmadaStep cfg apps (.reclaim t l v) s (s.withNitroStatus t l n)
  /-- Nitro `Adjudicator.challenge` (go-nitro ForceMove.sol:38-76). -/
  | challenge {s : ArmadaState} (t : Token) (challenger : Participant) (c : FixedPart)
      (proof : SupportProof) (candidate : Nitro.State) (n : Adjudicator)
      (h : Nitro.Adjudicator.challenge apps (toNitro s t) challenger c proof candidate = some n) :
      ArmadaStep cfg apps (.challenge t challenger c proof candidate) s (s.withNitroStatus t c n)
  /-- Nitro `Adjudicator.checkpoint` (go-nitro ForceMove.sol:85-114). -/
  | checkpoint {s : ArmadaState} (t : Token) (c : FixedPart) (proof : SupportProof)
      (candidate : Nitro.State) (n : Adjudicator)
      (h : Nitro.Adjudicator.checkpoint apps (toNitro s t) c proof candidate = some n) :
      ArmadaStep cfg apps (.checkpoint t c proof candidate) s (s.withNitroStatus t c n)
  /-- Nitro `Adjudicator.conclude` (go-nitro ForceMove.sol:136-164). -/
  | conclude {s : ArmadaState} (t : Token) (c : FixedPart) (ss : SignedState) (n : Adjudicator)
      (h : (toNitro s t).conclude c ss = some n) :
      ArmadaStep cfg apps (.conclude t c ss) s (s.withNitroStatus t c n)
  /-- Nitro `Adjudicator.tick`: the clock moves. -/
  | tick {s : ArmadaState} (dt : Time) :
      ArmadaStep cfg apps (.tick dt) s { s with now := s.now + dt }

/-- Some call takes `s` to `s'`. -/
def AnyStep (cfg : Config) (apps : Apps) (s s' : ArmadaState) : Prop :=
  ∃ call, ArmadaStep cfg apps call s s'

/-- The states reachable from a deployment into a reachable pool state, by any
    sequence of calls (Mathlib `Relation.ReflTransGen`). Every history is
    possible: the model has no forks and no finality (ruling 5). -/
def ArmadaReachable (cfg : Config) (apps : Apps) (s : ArmadaState) : Prop :=
  ∃ ps, _root_.Reachable ps ∧ Relation.ReflTransGen (AnyStep cfg apps) (genesis ps) s

/-- The call `call` can execute at `s`. -/
def CallEnabled (cfg : Config) (apps : Apps) (s : ArmadaState) (call : Call) : Prop :=
  ∃ s', ArmadaStep cfg apps call s s'

end ArmadaLean.ArmadaNitro
