/-
  Nitro protocol specification: the adjudicator and its on-chain operations.
  See `Address.lean` for the source list.

  Every operation is a function to `Option Adjudicator`. `none` means the
  call fails and the chain state is unchanged (S1:685-686: "making an invalid
  move is equivalent to not making any move at all"; S2:771-772: "T(A, B, x)
  fails, leaving the on-chain state unchanged").

  Modelling choice (apps). The deployed applications are a function
  `apps : AppId → Rules`. The adjudicator reads the rules of a channel
  through `c.appDef` (S3:304 `Application.at(state.appDef)`).
-/
import ArmadaLean.Nitro.Channel

namespace ArmadaLean.Nitro

/- `Rules.supports` is a `Prop`. The operations that read it decide it
   classically. -/
open Classical

/-- The deployed applications. S3:252-254: "A state channel application is a
    smart contract implementing `latestSupportedState`". -/
abbrev Apps := AppId → Rules

/-- The adjudicator. S2:149-164: one contract stores a balance per address
    and the finalized outcomes. S3:240-241: adjudication states in a mapping
    `statusOf` keyed by channel id. `held` is the total of coins the contract
    holds (S2:230-231). `now` is the chain clock (S1:1294-1296). -/
structure Adjudicator where
  balances : Balances
  held : Coins
  status : List (FixedPart × ChannelStatus)
  now : Time

/-- S3:240-241 `statusOf`. A channel with no record is open at turn 0. -/
def Adjudicator.statusOf (s : Adjudicator) (c : FixedPart) : ChannelStatus :=
  (s.status.lookup c).getD (.open 0)

/-- Write one channel's status. -/
def Adjudicator.setStatus (s : Adjudicator) (c : FixedPart) (st : ChannelStatus) : Adjudicator :=
  { s with status := (c, st) :: s.status.filter (fun e => decide (e.1 ≠ c)) }

/-- S2:602-603 `⟦χ ↦ Ω⟧`: the finalized outcome of a channel address. A
    participant address has no outcome. -/
def Adjudicator.finalOutcome (s : Adjudicator) (a : Address) : Option Outcome :=
  match a with
  | .participant _ => none
  | .channel c => (s.statusOf c).finalOutcome s.now

/-- The mode of a channel at the chain's current time. -/
def Adjudicator.mode (s : Adjudicator) (c : FixedPart) : Mode :=
  (s.statusOf c).mode s.now

/-- S2:395-398: "where the channel L itself has enough coins in the
    adjudicator to cover the entire allocation. In this case, we say the
    channel is directly funded." -/
def Adjudicator.DirectlyFunded (s : Adjudicator) (c : FixedPart) : Prop :=
  ∃ o, s.finalOutcome c.address = some (.allocation o) ∧ o.total ≤ s.balances.get c.address

/-- S2:480-481 "directly funded with x coins": the channel holds `x`. -/
def Adjudicator.DirectlyFundedWith (s : Adjudicator) (c : FixedPart) (x : Coins) : Prop :=
  x ≤ s.balances.get c.address

/-- The empty adjudicator. -/
def Adjudicator.genesis : Adjudicator :=
  { balances := [], held := 0, status := [], now := 0 }

/-- S2:165-168 `D_A(x)`: raise `A`'s balance by `x`. "There are no
    restrictions on who can deposit coins for an address, but the transaction
    must always include a transfer of x coins into the adjudicator." -/
def Adjudicator.deposit (s : Adjudicator) (a : Address) (x : Coins) : Adjudicator :=
  { s with balances := s.balances.add a x, held := s.held + x }

/-- S2:169-199 `W_A(x)`: withdraw `x` coins held at participant address `A`
    "by any party with the knowledge of the corresponding private key". The
    caller must be `A` (the signature is the caller's). S2:227-229: only from
    a participant address. The balance must cover `x`. -/
def Adjudicator.withdraw (s : Adjudicator) (caller : Participant) (a : Participant) (x : Coins) :
    Option Adjudicator :=
  if caller = a ∧ x ≤ s.balances.get (.participant a) then
    some { s with balances := s.balances.sub (.participant a) x, held := s.held - x }
  else
    none

/-- S2:765-772 `T(A, B, x)`: "If A can afford x for B, then T(A, B, x):
    1. Reduces the funds held in channel A by x. 2. Increases the funds held
    by B by x. 3. Reduces the amount owed to B in the outcome of A by x. If A
    cannot afford x for B, then T(A, B, x) fails, leaving the on-chain state
    unchanged." `A` must be a channel with a finalized allocation
    (S2:261-266). -/
def Adjudicator.transfer (s : Adjudicator) (a : FixedPart) (b : Address) (x : Coins) :
    Option Adjudicator :=
  match s.finalOutcome a.address with
  | some (.allocation o) =>
    if o.Affords (s.balances.get a.address) b x then
      some { (s.setStatus a ((s.statusOf a).withOutcome (.allocation (o.reduceOwed b x)))) with
        balances := (s.balances.sub a.address x).add b x }
    else
      none
  | _ => none

/-- S2:1139-1145 `C(G, A, x)`: "If G acts as guarantee for L and can afford x
    for A, then C(G, A, x) has the following three effects: Reduces the funds
    held in channel G by x. Increases the funds held in channel A by x.
    Reduces the amount owed to A in the outcome of L by x. Otherwise, the
    claim operation has no effect." S2:1072-1074: the target `L` must be
    finalized. -/
def Adjudicator.claim (s : Adjudicator) (g : FixedPart) (a : Address) (x : Coins) :
    Option Adjudicator :=
  match s.finalOutcome g.address with
  | some (.guarantee (.channel l) priority) =>
    match s.finalOutcome (.channel l) with
    | some (.allocation target) =>
      if GuaranteeAffords (s.balances.get g.address) priority target a x then
        some { (s.setStatus l ((s.statusOf l).withOutcome
            (.allocation (target.reduceOwed a x)))) with
          balances := (s.balances.sub g.address x).add a x }
      else
        none
    | _ => none
  | _ => none

/-- S3:344-364 `reclaim(ledgerChannelId, targetChannelId)` (Listing 2). Both
    channels must be finalized. The ledger's entry for the target must be a
    guarantee `G(x, [left, right])`. Then `o_ledger[left] += o_target[0]`,
    `o_ledger[right] += o_target[1]`, and the guarantee entry is deleted.
    The balances do not change. -/
def Adjudicator.reclaim (s : Adjudicator) (l v : FixedPart) : Option Adjudicator :=
  match s.finalOutcome l.address, s.finalOutcome v.address with
  | some (.allocation oLedger), some (.allocation oTarget) =>
    match oLedger.find v.address with
    | some ⟨_, .guarantee _ [left, right]⟩ =>
      let o1 := oLedger.addTo left (oTarget.amountAt 0)
      let o2 := o1.addTo right (oTarget.amountAt 1)
      some (s.setStatus l ((s.statusOf l).withOutcome (.allocation (o2.remove v.address))))
    | _ => none
  | _, _ => none

/-- S3:300-315 `challenge` (Listing 1) with S1:1340-1354 `forceMove`. The
    channel must be open (S3:303), the proof must support the candidate
    (S3:304), and the candidate's turn must be at least the recorded one
    (S3:305). The challenger must be a participant (S1:1545-1548, the
    certificate extension). The result stores the candidate with
    `deadline = now + challengeDuration` (S3:308-310; S1:1353
    `now() + defaultExpirationTime`). -/
noncomputable def Adjudicator.challenge (apps : Apps) (s : Adjudicator) (challenger : Participant)
    (c : FixedPart) (proof : SupportProof) (candidate : State) : Option Adjudicator :=
  if challenger ∈ c.participants ∧ (s.statusOf c).IsOpen s.now ∧
      (apps c.appDef).supports c proof candidate ∧ candidate.channel = c ∧
      (s.statusOf c).turnNumRecord ≤ candidate.turnNum then
    some (s.setStatus c (.challenged candidate.turnNum ⟨candidate, s.now + c.challengeDuration⟩))
  else
    none

/-- S1:1431-1440 `respondWithMove` and S1:1399-1408 `refute`: during a
    challenge, a supported state with a higher turn number cancels the
    challenge (S1:1377-1381: "each of these responses lead to an increase in
    the turnNum from the challenge state"). S1:1765-1770 `cancelChallenge`
    returns the channel to no-challenge. S1:1543-1545: the response's turn
    number is stored. When the channel is open the same call only raises the
    stored turn number. -/
noncomputable def Adjudicator.respond (apps : Apps) (s : Adjudicator) (c : FixedPart)
    (proof : SupportProof) (candidate : State) : Option Adjudicator :=
  if (s.statusOf c).IsOpen s.now ∧
      (apps c.appDef).supports c proof candidate ∧ candidate.channel = c ∧
      (s.statusOf c).turnNumRecord < candidate.turnNum then
    some (s.setStatus c (.open candidate.turnNum))
  else
    none

/-- S1:1495-1507 `conclude`: a valid conclusion proof on a non-terminated
    channel finalizes it at once (`setChallenge(endState, now())`).
    S2:296-299: "any participant can then register this outcome on-chain to
    create a finalized outcome." S3:286-289: "supporting a state with
    `isFinal = true` and submitting the support proof to a Conclude
    operation." -/
noncomputable def Adjudicator.conclude (apps : Apps) (s : Adjudicator) (c : FixedPart)
    (proof : SupportProof) (candidate : State) : Option Adjudicator :=
  if (s.statusOf c).IsOpen s.now ∧
      (apps c.appDef).supports c proof candidate ∧ candidate.channel = c ∧
      candidate.isFinal = true then
    some (s.setStatus c (.finalized candidate.turnNum candidate.outcome))
  else
    none

/-- The chain clock moves forward. S1:1261-1265: a challenge that receives no
    response "within the timeout period" terminates. -/
def Adjudicator.tick (s : Adjudicator) (dt : Time) : Adjudicator :=
  { s with now := s.now + dt }

/-- An on-chain operation. S2:1139-1140: "the claim operation ... to the
    existing transfer, deposit and withdraw operations"; S1:1285-1290 lists
    `forceMove`, `refute`, `respondWithMove`, `alternativeRespondWithMove`,
    `withdraw`; S3 adds `reclaim`. -/
inductive Op
  | deposit (a : Address) (x : Coins)
  | withdraw (a : Participant) (x : Coins)
  | transfer (a : FixedPart) (b : Address) (x : Coins)
  | claim (g : FixedPart) (a : Address) (x : Coins)
  | reclaim (l v : FixedPart)
  | challenge (c : FixedPart) (proof : SupportProof) (candidate : State)
  | respond (c : FixedPart) (proof : SupportProof) (candidate : State)
  | conclude (c : FixedPart) (proof : SupportProof) (candidate : State)
  | tick (dt : Time)

/-- The signed states an operation submits. -/
def Op.proofStates : Op → SupportProof
  | .challenge _ proof _ => proof
  | .respond _ proof _ => proof
  | .conclude _ proof _ => proof
  | _ => []

/-- S2:312-313: "There is no restriction on who can trigger the operations."
    The redistribution operations ignore the caller. -/
def Op.isRedistribution : Op → Bool
  | .transfer .. => true
  | .claim .. => true
  | .reclaim .. => true
  | _ => false

/-- Apply one operation by one caller. -/
noncomputable def Adjudicator.apply (apps : Apps) (caller : Participant) (op : Op) (s : Adjudicator) :
    Option Adjudicator :=
  match op with
  | .deposit a x => some (s.deposit a x)
  | .withdraw a x => s.withdraw caller a x
  | .transfer a b x => s.transfer a b x
  | .claim g a x => s.claim g a x
  | .reclaim l v => s.reclaim l v
  | .challenge c proof candidate => s.challenge apps caller c proof candidate
  | .respond c proof candidate => s.respond apps c proof candidate
  | .conclude c proof candidate => s.conclude apps c proof candidate
  | .tick dt => some (s.tick dt)

/-- One successful on-chain step. -/
inductive Step (apps : Apps) : Adjudicator → Adjudicator → Prop
  | mk (caller : Participant) (op : Op) (s s' : Adjudicator)
      (h : s.apply apps caller op = some s') : Step apps s s'

/-- The states reachable from genesis. -/
inductive Reachable (apps : Apps) : Adjudicator → Prop
  | genesis : Reachable apps Adjudicator.genesis
  | step {s s'} : Reachable apps s → Step apps s s' → Reachable apps s'

/-- Apply a list of (caller, op) pairs. A failed operation changes nothing
    and the sequence continues. -/
noncomputable def Adjudicator.applyAll (apps : Apps) : List (Participant × Op) → Adjudicator → Adjudicator
  | [], s => s
  | (caller, op) :: rest, s => Adjudicator.applyAll apps rest ((s.apply apps caller op).getD s)

end ArmadaLean.Nitro
