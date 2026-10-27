/-
  Armada adjudicator: the calls and the step relation. See `Notes.lean` for
  the design summary and `docs/armada-nitro-theorems.md` for the theorem map.

  The call set is the Nitro operation set (Nitro `Adjudicator.lean`: deposit,
  transfer, reclaim, challenge, checkpoint, conclude, tick), one call per
  token, plus `env`, a pool step by another pool user. There is no separate
  merge call and no batch call (operator ruling 2026-10-27, 1 and 3). A batch
  is a sequence of calls; `ArmadaReachable` covers every sequence.

  A call label holds what a caller submits: the token, the channel, the notes
  that the call spends, and the amounts. A pool proof names the nullifiers of
  the notes it spends and fixes the values of the notes it creates, so these
  belong to the submitted call. The pool chooses the keys of the created
  notes; they are witnesses of the step.

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
    * `transfer t c b ins x`: go-nitro `transfer` (MultiAssetHolder.sol:72-100)
      of channel `c`'s entry for `b`, paid from the channel notes `ins`. `x` is
      the payout amount. The pool proof fixes it, because the proof fixes the
      values of its output notes.
    * `reclaim`, `challenge`, `checkpoint`, `conclude`: the Nitro operations of
      the same names, for token `t`.
    * `tick dt`: the chain clock moves. -/
inductive Call
  | env
  | deposit (t : Token) (c : FixedPart) (expectedHeld x : Coins) (fund merged : List Note)
  | transfer (t : Token) (c : FixedPart) (b : Address) (ins : List Note) (x : Coins)
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
  | .transfer t' c b _ _ => if t' = t then some (.transfer c b) else none
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

/-- The outcome of the candidate state that a challenge, checkpoint or
    conclude submits. Other calls submit no state. -/
def Call.candidateOutcome : Call → Option Outcome
  | .challenge _ _ _ _ candidate => some candidate.outcome
  | .checkpoint _ _ _ candidate => some candidate.outcome
  | .conclude _ _ ss => some ss.state.outcome
  | _ => none

/-- One entry obeys the outcome rule (operator ruling 2026-10-27 on finding F6,
    option A): an allocation item to a channel destination is 0 or at least
    `cfg.minCredit`. A participant destination has no minimum. A guarantee
    item is not paid by a transfer (Nitro `transfer_fails_otherwise`), so the
    rule does not apply to it; the amounts that a reclaim moves out of a
    guarantee are `ReclaimCreditsRespectMin`. -/
def EntryRespectsMin (cfg : Config) (e : Entry) : Prop :=
  e.dest.isParticipant = false → e.item.isGuarantee = false →
    e.amount = 0 ∨ cfg.minCredit ≤ e.amount

instance (cfg : Config) (e : Entry) : Decidable (EntryRespectsMin cfg e) :=
  inferInstanceAs (Decidable (e.dest.isParticipant = false → e.item.isGuarantee = false →
    e.amount = 0 ∨ cfg.minCredit ≤ e.amount))

/-- The outcome rule: every entry obeys `EntryRespectsMin`. The adjudicator
    decides it (`Decidable` instance below). -/
def OutcomeRespectsMin (cfg : Config) (o : Allocation) : Prop :=
  ∀ e ∈ o, EntryRespectsMin cfg e

instance (cfg : Config) (o : Allocation) : Decidable (OutcomeRespectsMin cfg o) :=
  inferInstanceAs (Decidable (∀ e ∈ o, EntryRespectsMin cfg e))

/-- The amounts that a reclaim of a guarantee `G(x, [left, right])` against the
    target outcome `oV` adds to the ledger's entries for `left` and `right`
    (Nitro `Adjudicator.reclaim`: `oV.amountAt 0` and `oV.amountAt 1`) obey
    the minimum when the destination is a channel. A reclaim does not check
    this (design choice D14); it is the hypothesis under which a reclaim keeps
    the outcome rule. -/
def ReclaimCreditsRespectMin (cfg : Config) (oV : Allocation) (left right : Address) : Prop :=
  (left.isParticipant = false → oV.amountAt 0 = 0 ∨ cfg.minCredit ≤ oV.amountAt 0) ∧
  (right.isParticipant = false → oV.amountAt 1 = 0 ∨ cfg.minCredit ≤ oV.amountAt 1)

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

/-- The minimum-credit rule (operator ruling 2026-10-27, armada-laconic
    `labbook/2026-10-27-payout-griefing.md`): a credit of `x` into a channel
    `d` that is already finalized needs `cfg.minCredit ≤ x`. A payment to a
    participant has no minimum. The rule reads only the adjudicator's record
    and the clock, not the pool. -/
def CreditAllowed (cfg : Config) (s : ArmadaState) (t : Token) : Address → Coins → Prop
  | .participant _, _ => True
  | .channel d, x => (s.chanOf t d).status.mode s.now = .finalized → cfg.minCredit ≤ x

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
      `transfer_zero_moves_nothing`). The call spends no note and creates no
      note, so it credits nothing and cannot make another caller's pending
      payout stale. -/
  | transferZero {s : ArmadaState} (t : Token) (c : FixedPart) (b : Address) (o : Allocation)
      (hFin : (s.chanOf t c).status.finalOutcome s.now = some (.allocation o))
      (hEntry : ∃ amt, o.find b = some ⟨b, .alloc amt⟩)
      (hZero : s.payout t c o b = 0) :
      ArmadaStep cfg apps (.transfer t c b [] 0) s
        (s.setChan t c { s.chanOf t c with
          status := (s.chanOf t c).status.withOutcome (.allocation (o.reduceOwed b 0)) })
  /-- Transfer (go-nitro MultiAssetHolder.sol:72-100; Nitro:765-772). The
      channel is finalized with an allocation that has an allocation entry for
      `b` (ruling 3). Payout rule B (operator ruling 2026-10-27): the submitted
      amount `x` is exactly the affordable amount, and `x > 0`. A credit into
      a finalized channel is at least `cfg.minCredit` (`hCredit`). The two
      checks read only the adjudicator's record (`transfer_wrong_amount_fails`,
      `credit_below_minimum_fails`). The call spends only the channel notes
      `ins`. It creates the payout note `pay` of value `x` with the note key
      of `b` (ruling 4) and the change note `change`, the one note that goes
      back to the channel (ruling 3). -/
  | transfer {s : ArmadaState} (t : Token) (c : FixedPart) (b : Address) (o : Allocation)
      (ins keep : List Note) (x : Coins) (ps' : PoolState) (pay change : Note)
      (hFin : (s.chanOf t c).status.finalOutcome s.now = some (.allocation o))
      (hEntry : ∃ amt, o.find b = some ⟨b, .alloc amt⟩)
      (hX : s.payout t c o b = x) (hPos : 0 < x) (hCredit : CreditAllowed cfg s t b x)
      (hIns : (s.chanOf t c).notes.Perm (ins ++ keep))
      (hCall : PoolCall s.pool ps' t ins [pay, change])
      (hPay : pay.2.value = x ∧ PayKey cfg b pay.2)
      (hChange : OwnedBy cfg.self change.2) :
      ArmadaStep cfg apps (.transfer t c b ins x) s
        (({ s with pool := ps' }.setChan t c
            { status := (s.chanOf t c).status.withOutcome (.allocation (o.reduceOwed b x)),
              notes := keep ++ [change] }).credit t b pay)
  /-- Nitro `Adjudicator.reclaim` (SATP Listing 2; go-nitro `reclaim`). No
      outcome-rule check (design choice D14). -/
  | reclaim {s : ArmadaState} (t : Token) (l v : FixedPart) (n : Adjudicator)
      (h : (toNitro s t).reclaim l v = some n) :
      ArmadaStep cfg apps (.reclaim t l v) s (s.withNitroStatus t l n)
  /-- Nitro `Adjudicator.challenge` (go-nitro ForceMove.sol:38-76), plus the
      Armada outcome rule on the candidate (`hMin`; operator ruling
      2026-10-27 on F6). The adjudicator rejects a candidate that breaks the
      rule as it rejects an unsupported candidate. -/
  | challenge {s : ArmadaState} (t : Token) (challenger : Participant) (c : FixedPart)
      (proof : SupportProof) (candidate : Nitro.State) (n : Adjudicator)
      (h : Nitro.Adjudicator.challenge apps (toNitro s t) challenger c proof candidate = some n)
      (hMin : OutcomeRespectsMin cfg candidate.outcome.entries) :
      ArmadaStep cfg apps (.challenge t challenger c proof candidate) s (s.withNitroStatus t c n)
  /-- Nitro `Adjudicator.checkpoint` (go-nitro ForceMove.sol:85-114), plus the
      Armada outcome rule on the candidate (`hMin`). -/
  | checkpoint {s : ArmadaState} (t : Token) (c : FixedPart) (proof : SupportProof)
      (candidate : Nitro.State) (n : Adjudicator)
      (h : Nitro.Adjudicator.checkpoint apps (toNitro s t) c proof candidate = some n)
      (hMin : OutcomeRespectsMin cfg candidate.outcome.entries) :
      ArmadaStep cfg apps (.checkpoint t c proof candidate) s (s.withNitroStatus t c n)
  /-- Nitro `Adjudicator.conclude` (go-nitro ForceMove.sol:136-164), plus the
      Armada outcome rule on the concluded state (`hMin`). -/
  | conclude {s : ArmadaState} (t : Token) (c : FixedPart) (ss : SignedState) (n : Adjudicator)
      (h : (toNitro s t).conclude c ss = some n)
      (hMin : OutcomeRespectsMin cfg ss.state.outcome.entries) :
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

/-- A sequence of steps with its list of calls, from `s` to `s'`. Mathlib's
    `Relation.ReflTransGen` does not record the labels; the counting theorem
    needs them. -/
inductive Steps (cfg : Config) (apps : Apps) : ArmadaState → List Call → ArmadaState → Prop
  | nil {s : ArmadaState} : Steps cfg apps s [] s
  | cons {s s1 s' : ArmadaState} {call : Call} {calls : List Call} :
      ArmadaStep cfg apps call s s1 → Steps cfg apps s1 calls s' →
        Steps cfg apps s (call :: calls) s'

/-- The call is a payout of a positive amount on channel `c` in token `t`. -/
def Call.isPayoutOn (t : Token) (c : FixedPart) : Call → Bool
  | .transfer t' c' _ _ x => decide (t' = t) && decide (c' = c) && decide (0 < x)
  | _ => false

/-- The call is a reclaim with ledger channel `c` in token `t`. -/
def Call.isReclaimAgainst (t : Token) (c : FixedPart) : Call → Bool
  | .reclaim t' l _ => decide (t' = t) && decide (l = c)
  | _ => false

/-- The call credits a positive amount into channel `c` in token `t`: a payout
    of any channel, `c` included, whose destination is `c`. -/
def Call.isCreditTo (t : Token) (c : FixedPart) : Call → Bool
  | .transfer t' _ b _ x => decide (t' = t) && decide (b = c.address) && decide (0 < x)
  | _ => false

/-- The number of guarantee items in an allocation (SATP:322-323). -/
def guaranteeCount (o : Allocation) : Nat :=
  (o.filter (fun e => e.item.isGuarantee)).length

end ArmadaLean.ArmadaNitro
