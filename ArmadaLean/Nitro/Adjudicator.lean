/-
  Nitro protocol specification: the adjudicator and its on-chain operations.
  See `Address.lean` for the source list. The operation set is go-nitro's
  `NitroAdjudicator` (ForceMove.sol: `challenge`, `checkpoint`, `conclude`;
  MultiAssetHolder.sol: `deposit`, `transfer`, `reclaim`). Nitro:1139 `claim`
  is not modelled: SATP and go-nitro replaced it by `reclaim` (operator
  ruling 2026-10-27).

  Every operation is a function to `Option Adjudicator`. `none` means the
  call reverts and the chain state is unchanged (go-nitro `require`;
  Nitro:771-772; ForceMove:685-686).

  Modelling choice (apps). The deployed applications are a function
  `apps : AppId → Rules`. The adjudicator reads the rules of a channel
  through `c.appDef` (go-nitro ForceMove.sol
  `IForceMoveApp(fixedPart.appDefinition)`; SATP:304).
-/
import Mathlib.Logic.Relation
import ArmadaLean.Nitro.Channel

namespace ArmadaLean.Nitro

/-- The deployed applications. SATP:252-254; go-nitro IForceMoveApp.sol. -/
abbrev Apps := AppId → Rules

/-- The adjudicator. go-nitro: `holdings` per channel (MultiAssetHolder.sol:23)
    and `statusOf` per channel id (StatusManager.sol); SATP:240-241;
    Nitro:149-164. `held` is the total of coins the contract holds
    (Nitro:230-231). `now` is `block.timestamp`. -/
structure Adjudicator where
  balances : Balances
  held : Coins
  status : List (FixedPart × ChannelStatus)
  now : Time

/-- SATP:240-241 `statusOf`; go-nitro `statusOf`. A channel with no record
    is open at turn 0 (go-nitro: an empty status unpacks to zeros). -/
def Adjudicator.statusOf (s : Adjudicator) (c : FixedPart) : ChannelStatus :=
  (s.status.lookup c).getD (.open 0)

/-- Write one channel's status. -/
def Adjudicator.setStatus (s : Adjudicator) (c : FixedPart) (st : ChannelStatus) : Adjudicator :=
  { s with status := (c, st) :: s.status.filter (fun e => decide (e.1 ≠ c)) }

/-- Nitro:602-603 `⟦χ ↦ Ω⟧`: the finalized outcome of a channel address. A
    participant address has no outcome. -/
def Adjudicator.finalOutcome (s : Adjudicator) (a : Address) : Option Outcome :=
  match a with
  | .participant _ => none
  | .channel c => (s.statusOf c).finalOutcome s.now

/-- The mode of a channel at the chain's current time. -/
def Adjudicator.mode (s : Adjudicator) (c : FixedPart) : Mode :=
  (s.statusOf c).mode s.now

/-- Nitro:395-398: "where the channel L itself has enough coins in the
    adjudicator to cover the entire allocation. In this case, we say the
    channel is directly funded." -/
def Adjudicator.DirectlyFunded (s : Adjudicator) (c : FixedPart) : Prop :=
  ∃ o, s.finalOutcome c.address = some (.allocation o) ∧ o.total ≤ s.balances.get c.address

/-- Nitro:480-481 "directly funded with x coins": the channel holds `x`. -/
def Adjudicator.DirectlyFundedWith (s : Adjudicator) (c : FixedPart) (x : Coins) : Prop :=
  x ≤ s.balances.get c.address

/-- The empty adjudicator. -/
def Adjudicator.genesis : Adjudicator :=
  { balances := [], held := 0, status := [], now := 0 }

/-- go-nitro MultiAssetHolder.sol:36-62 `deposit`: raise the holding of a
    channel by `amount`; "Deposit to external destination" reverts
    (line 43). Nitro:165-168 `D_A(x)`: "There are no restrictions on who can
    deposit coins for an address, but the transaction must always include a
    transfer of x coins into the adjudicator"; Nitro:227-228 allows either
    address kind. The code is followed: only a channel address. SATP:764-768
    defers deposits. The `expectedHeld` check (line 51) is reorg protection
    and is not modelled. -/
def Adjudicator.deposit (s : Adjudicator) (a : Address) (x : Coins) : Option Adjudicator :=
  match a with
  | .channel _ => some { s with balances := s.balances.add a x, held := s.held + x }
  | .participant _ => none

/-- Pay `x` coins to a destination. go-nitro `_executeSingleAssetExit`
    (MultiAssetHolder.sol:396-408): an external destination receives the
    asset from the contract; a channel destination's holding rises. There
    is no withdrawal operation in go-nitro: Nitro:169-199 `W_A(x)` is
    realized by this payout, and SATP:764-768 defers withdrawals. -/
def Adjudicator.payTo (s : Adjudicator) (b : Address) (x : Coins) : Adjudicator :=
  match b with
  | .participant _ => { s with balances := s.balances.add b x, held := s.held - x }
  | .channel _ => { s with balances := s.balances.add b x }

/-- go-nitro MultiAssetHolder.sol:72-100 `transfer`: on a finalized channel,
    pay a selected allocation entry "as many funds escrowed against
    `channelId` as can be afforded" (line 66), in priority order
    (`compute_transfer_effects_and_interactions`, lines 162-191); a guarantee
    entry cannot be transferred (line 171-172). Nitro:765-772 `T(A, B, x)`
    with `x ≤` the affordable amount; the code pays the whole affordable
    amount, so `x` is not a parameter. SATP:764-768 defers payouts. The
    multi-index batch (`indices`) is an encoding and is not modelled. -/
def Adjudicator.transfer (s : Adjudicator) (a : FixedPart) (b : Address) : Option Adjudicator :=
  match s.finalOutcome a.address with
  | some (.allocation o) =>
    match o.find b with
    | some ⟨_, .alloc _⟩ =>
      let x := o.paidTo (s.balances.get a.address) b
      some (((s.setStatus a ((s.statusOf a).withOutcome (.allocation (o.reduceOwed b x)))).payTo b x)
        |> fun s' => { s' with balances := s'.balances.sub a.address x })
    | _ => none
  | _ => none

/-- SATP:344-364 `reclaim(ledgerChannelId, targetChannelId)` (Listing 2) as
    corrected by go-nitro `reclaim` and `compute_reclaim_effects`
    (MultiAssetHolder.sol:233-370). Both channels are finalized. The ledger's
    entry for the target is a guarantee `G(x, [left, right])`. Then
    `o_ledger[left] += o_target[0]`, `o_ledger[right] += o_target[1]`, and
    the guarantee entry is deleted. go-nitro adds three checks SATP lacks:
    `left` and `right` must have entries in the ledger (lines 363-364) and
    `o_target[0] + o_target[1] = x` (line 365). The balances do not change
    (line 391: "no changes are made to the target channel"; the ledger's
    holding is untouched). -/
def Adjudicator.reclaim (s : Adjudicator) (l v : FixedPart) : Option Adjudicator :=
  match s.finalOutcome l.address, s.finalOutcome v.address with
  | some (.allocation oLedger), some (.allocation oTarget) =>
    match oLedger.find v.address with
    | some ⟨_, .guarantee x [left, right]⟩ =>
      if (oLedger.remove v.address).find left ≠ none ∧
          (oLedger.remove v.address).find right ≠ none ∧
          oTarget.amountAt 0 + oTarget.amountAt 1 = x then
        let o1 := oLedger.addTo left (oTarget.amountAt 0)
        let o2 := o1.addTo right (oTarget.amountAt 1)
        some (s.setStatus l ((s.statusOf l).withOutcome (.allocation (o2.remove v.address))))
      else
        none
    | _ => none
  | _, _ => none

/-- go-nitro ForceMove.sol:38-76 `challenge`: in Open mode the candidate's
    turn must not decrease the record; in Challenge mode it must increase
    it; in Finalized mode the call reverts. The application must support the
    candidate, and the challenger must be a participant
    (`_requireChallengerIsParticipant`). The status becomes the candidate's
    turn, `block.timestamp + challengeDuration`. SATP:300-315 (Listing 1)
    allows a re-challenge at an equal version while a challenge runs, which
    lets a participant push the deadline forever; the code corrects it.
    ForceMove:1340-1354 forbids a challenge while one runs; the code allows
    one at a higher turn. -/
def Adjudicator.challenge (apps : Apps) (s : Adjudicator) (challenger : Participant)
    (c : FixedPart) (proof : SupportProof) (candidate : State) : Option Adjudicator :=
  if challenger ∈ c.participants ∧
      (apps c.appDef).supports c proof candidate = true ∧ candidate.channel = c ∧
      ((s.mode c = .open ∧ (s.statusOf c).turnNumRecord ≤ candidate.turnNum) ∨
       (s.mode c = .challenge ∧ (s.statusOf c).turnNumRecord < candidate.turnNum)) then
    some (s.setStatus c (.challenged candidate.turnNum ⟨candidate, s.now + c.challengeDuration⟩))
  else
    none

/-- go-nitro ForceMove.sol:85-114 `checkpoint`: the channel is not
    finalized, the candidate's turn is strictly higher than the record, and
    the application supports the candidate. The status becomes Open at the
    candidate's turn; a running challenge is cleared. SATP has no such
    operation. ForceMove:1399-1440 `refute` and `respondWithMove` and
    ForceMove:1543-1545 ("store the turnNum of the response state") are
    superseded by it. -/
def Adjudicator.checkpoint (apps : Apps) (s : Adjudicator) (c : FixedPart)
    (proof : SupportProof) (candidate : State) : Option Adjudicator :=
  if (s.statusOf c).IsOpen s.now ∧
      (apps c.appDef).supports c proof candidate = true ∧ candidate.channel = c ∧
      (s.statusOf c).turnNumRecord < candidate.turnNum then
    some (s.setStatus c (.open candidate.turnNum))
  else
    none

/-- go-nitro ForceMove.sol:136-164 `_conclude`: the channel is not
    finalized, the candidate is final, and every participant signed it; the
    application is not called. The channel finalizes at once with the
    candidate's outcome. SATP:286-289: "supporting a state with isFinal =
    true and submitting the support proof to a Conclude operation";
    Nitro:296-300; ForceMove:1495-1507. go-nitro also resets the stored turn
    to 0; no operation reads the turn of a finalized channel, so the model
    keeps the candidate's turn. -/
def Adjudicator.conclude (s : Adjudicator) (c : FixedPart) (ss : SignedState) :
    Option Adjudicator :=
  if (s.statusOf c).IsOpen s.now ∧ ConclusionProof c ss then
    some (s.setStatus c (.finalized ss.state.turnNum ss.state.outcome))
  else
    none

/-- The chain clock moves forward. go-nitro reads `block.timestamp`;
    ForceMove:1261-1265: a challenge that receives no response "within the
    timeout period" terminates. -/
def Adjudicator.tick (s : Adjudicator) (dt : Time) : Adjudicator :=
  { s with now := s.now + dt }

/-- An on-chain operation. go-nitro NitroAdjudicator: `deposit`,
    `transfer`, `reclaim`, `challenge`, `checkpoint`, `conclude` (the batch
    helpers `transferAllAssets` and `concludeAndTransferAllAssets` are
    sequences of these). -/
inductive Op
  | deposit (a : Address) (x : Coins)
  | transfer (a : FixedPart) (b : Address)
  | reclaim (l v : FixedPart)
  | challenge (c : FixedPart) (proof : SupportProof) (candidate : State)
  | checkpoint (c : FixedPart) (proof : SupportProof) (candidate : State)
  | conclude (c : FixedPart) (ss : SignedState)
  | tick (dt : Time)

/-- The signed states an operation submits. -/
def Op.proofStates : Op → SupportProof
  | .challenge _ proof _ => proof
  | .checkpoint _ proof _ => proof
  | .conclude _ ss => [ss]
  | _ => []

/-- Nitro:312-313: "There is no restriction on who can trigger the
    operations." go-nitro `transfer` and `reclaim` have no caller check. -/
def Op.isRedistribution : Op → Bool
  | .transfer .. => true
  | .reclaim .. => true
  | _ => false

/-- Apply one operation by one caller. -/
def Adjudicator.apply (apps : Apps) (caller : Participant) (op : Op) (s : Adjudicator) :
    Option Adjudicator :=
  match op with
  | .deposit a x => s.deposit a x
  | .transfer a b => s.transfer a b
  | .reclaim l v => s.reclaim l v
  | .challenge c proof candidate => s.challenge apps caller c proof candidate
  | .checkpoint c proof candidate => s.checkpoint apps c proof candidate
  | .conclude c ss => s.conclude c ss
  | .tick dt => some (s.tick dt)

/-- One successful on-chain step. -/
inductive Step (apps : Apps) : Adjudicator → Adjudicator → Prop
  | mk (caller : Participant) (op : Op) (s s' : Adjudicator)
      (h : s.apply apps caller op = some s') : Step apps s s'

/-- The states reachable from genesis: the reflexive transitive closure of
    `Step` (Mathlib `Relation.ReflTransGen`). -/
def Reachable (apps : Apps) (s : Adjudicator) : Prop :=
  Relation.ReflTransGen (Step apps) Adjudicator.genesis s

/-- Apply a list of (caller, op) pairs. A failed operation changes nothing
    and the sequence continues. -/
def Adjudicator.applyAll (apps : Apps) : List (Participant × Op) → Adjudicator → Adjudicator
  | [], s => s
  | (caller, op) :: rest, s => Adjudicator.applyAll apps rest ((s.apply apps caller op).getD s)

end ArmadaLean.Nitro
