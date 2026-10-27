/-
  Armada adjudicator: the state, and the abstraction to the Nitro
  `Adjudicator`. See `Notes.lean` for the design summary and
  `docs/armada-nitro-theorems.md` for the theorem map.

  A channel is an object with a status (the Nitro `ChannelStatus`, whose
  `mode` gives the phases open, challenge and finalized) and its own notes
  (operator ruling 2026-10-27, 3). The adjudicator stores no balance. A
  channel's balance is the total value of its notes (ruling 2). There is no
  `holdings` table and no stored hash of a state or an outcome: the status
  stores the outcome itself, as in the Nitro specification (layout audit
  findings A3, A6).

  Multi-asset is one independent copy per token (ruling 6; Nitro
  `Address.lean`, module comment). `ArmadaState.book t` is the copy for token
  `t`. The pool and the clock are shared.
-/
import ArmadaLean.ArmadaNitro.Notes

namespace ArmadaLean.ArmadaNitro

set_option autoImplicit false

open ArmadaLean.Nitro (Coins Time Participant FixedPart Address ChannelStatus Balances Adjudicator)

/-- One channel of one token: its status and its notes. -/
structure Channel where
  status : ChannelStatus
  notes : List Note

/-- A channel with no record: open at turn 0 with no notes. This matches
    Nitro `Adjudicator.statusOf` (Adjudicator.lean:31-33) and `Balances.get`
    (Address.lean:96-98) on an absent key. -/
def Channel.empty : Channel := ⟨.open 0, []⟩

/-- Operator ruling 2026-10-27, 2: a channel's balance is the total value of
    the adjudicator notes attributed to it. -/
def Channel.balance (ch : Channel) : Coins := notesValue ch.notes

/-- The adjudicator's record for one token.
    * `channels`: the channel objects, one entry per channel.
    * `payments`: ghost record of the notes the adjudicator created for
      participants (ruling 4). A participant's Nitro balance is the coins paid
      out to it (Nitro `Balances`, Address.lean:86-94); here it is the total
      value of these notes. -/
structure Holder where
  channels : List (FixedPart × Channel)
  payments : List (Participant × Note)

/-- The record before any call. -/
def Holder.empty : Holder := ⟨[], []⟩

/-- The channel object for `c`. -/
def Holder.chan (h : Holder) (c : FixedPart) : Channel :=
  (h.channels.lookup c).getD Channel.empty

/-- Write one channel object. Old entries for `c` are dropped, as in Nitro
    `Adjudicator.setStatus` (Adjudicator.lean:36-37). -/
def Holder.setChan (h : Holder) (c : FixedPart) (ch : Channel) : Holder :=
  { h with channels := (c, ch) :: h.channels.filter (fun e => decide (e.1 ≠ c)) }

/-- The notes the adjudicator paid to `p`. -/
def Holder.paymentsTo (h : Holder) (p : Participant) : List Note :=
  (h.payments.filter (fun e => decide (e.1 = p))).map (·.2)

/-- The coins paid out to `p`: the total value of its payment notes. -/
def Holder.paid (h : Holder) (p : Participant) : Coins := notesValue (h.paymentsTo p)

/-- The participants that received a payment, each once. -/
def Holder.payees (h : Holder) : List Participant := (h.payments.map (·.1)).eraseDups

/-- The Nitro balance table of this record: a channel entry is the channel's
    note total; a participant entry is the value paid to it. -/
def Holder.balances (h : Holder) : Balances :=
  h.channels.map (fun e => (e.1.address, e.2.balance)) ++
    h.payees.map (fun p => (.participant p, h.paid p))

/-- The coins the adjudicator holds for this token: the sum of the channel
    balances (Nitro:230-231). -/
def Holder.held (h : Holder) : Coins := (h.channels.map (fun e => e.2.balance)).sum

/-- The Nitro status table of this record. -/
def Holder.status (h : Holder) : List (FixedPart × ChannelStatus) :=
  h.channels.map (fun e => (e.1, e.2.status))

/-- Every note attributed to some channel of this record. -/
def Holder.attributed (h : Holder) : List Note :=
  (h.channels.map (fun e => e.2.notes)).flatten

/-- The Armada system: the pool, one adjudicator record per token, and the
    chain clock. -/
structure ArmadaState where
  pool : PoolState
  book : Token → Holder
  now : Time

/-- The channel object of `c` for token `t`. -/
def ArmadaState.chanOf (s : ArmadaState) (t : Token) (c : FixedPart) : Channel :=
  (s.book t).chan c

/-- The balance of channel `c` for token `t`. -/
def ArmadaState.balance (s : ArmadaState) (t : Token) (c : FixedPart) : Coins :=
  (s.chanOf t c).balance

/-- Write the channel object of `c` for token `t`. -/
def ArmadaState.setChan (s : ArmadaState) (t : Token) (c : FixedPart) (ch : Channel) :
    ArmadaState :=
  { s with book := fun t' => if t' = t then (s.book t).setChan c ch else s.book t' }

/-- Record a payment note for `p` in token `t`. -/
def ArmadaState.pay (s : ArmadaState) (t : Token) (p : Participant) (e : Note) : ArmadaState :=
  { s with book := fun t' =>
      if t' = t then { s.book t with payments := (p, e) :: (s.book t).payments } else s.book t' }

/-- Every note attributed to a channel of token `t`. -/
def ArmadaState.attributed (s : ArmadaState) (t : Token) : List Note := (s.book t).attributed

/-- The abstraction function: the Nitro adjudicator that the record of token
    `t` represents. Balances are note totals per channel. -/
def toNitro (s : ArmadaState) (t : Token) : Adjudicator :=
  { balances := (s.book t).balances, held := (s.book t).held,
    status := (s.book t).status, now := s.now }

/-- The deployment of the adjudicator into the pool state `ps`: no channel, no
    payment, clock 0 (Nitro `Adjudicator.genesis`, Adjudicator.lean:61-62). -/
def genesis (ps : PoolState) : ArmadaState :=
  { pool := ps, book := fun _ => Holder.empty, now := 0 }

/-- Two Nitro adjudicators that no Nitro operation can tell apart: the same
    balance at every address, the same coins held, the same status for every
    channel, the same time. Nitro operations read the state only through
    `Balances.get`, `held`, `statusOf` and `now` (Adjudicator.lean). The
    abstraction is exact up to this relation; the order of list entries is
    not observable. -/
def NitroEquiv (a b : Adjudicator) : Prop :=
  (∀ x, a.balances.get x = b.balances.get x) ∧ a.held = b.held ∧
    (∀ c, a.statusOf c = b.statusOf c) ∧ a.now = b.now

end ArmadaLean.ArmadaNitro
