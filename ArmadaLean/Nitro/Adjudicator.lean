/-
  Nitro protocol specification: the adjudicator and its on-chain operations.
  See `Address.lean` for the source list. The operation set is go-nitro's
  `NitroAdjudicator` (ForceMove.sol: `challenge`, `checkpoint`, `conclude`;
  MultiAssetHolder.sol: `deposit`, `transfer`, `reclaim`). Nitro:1139 `claim`
  is not modelled: SATP and go-nitro replaced it by `reclaim` (design
  decision 2026-10-27).

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

variable {E : Type}

/-- The deployed applications. SATP:252-254; go-nitro IForceMoveApp.sol. -/
abbrev Apps (E : Type) := AppId → Rules E

/-- The adjudicator. go-nitro: `holdings` per channel (MultiAssetHolder.sol:23)
    and `statusOf` per channel id (StatusManager.sol); SATP:240-241;
    Nitro:149-164. `held` is the total of coins the contract holds
    (Nitro:230-231). `now` is `block.timestamp`. -/
structure Adjudicator (E : Type) where
  balances : Balances E
  held : Coins
  status : List (FixedPart × ChannelStatus E)
  now : Time

/-- SATP:240-241 `statusOf`; go-nitro `statusOf`. A channel with no record
    is open at turn 0 (go-nitro: an empty status unpacks to zeros). -/
def Adjudicator.statusOf (s : Adjudicator E) (c : FixedPart) : ChannelStatus E :=
  (s.status.lookup c).getD (.open 0)

/-- Write one channel's status. -/
def Adjudicator.setStatus (s : Adjudicator E) (c : FixedPart) (st : ChannelStatus E) :
    Adjudicator E :=
  { s with status := (c, st) :: s.status.filter (fun e => decide (e.1 ≠ c)) }

/-- The stored outcome of a finalized channel address: the allocation that
    remains after payouts (Nitro:263-264). An external destination has no
    outcome. -/
def Adjudicator.finalOutcome (s : Adjudicator E) (a : Address E) : Option (Outcome E) :=
  match a with
  | .external _ => none
  | .channel c => (s.statusOf c).finalOutcome s.now

/-- Nitro:602-603 `⟦χ ↦ Ω⟧`: the outcome a channel address finalized with. -/
def Adjudicator.finalizedWith (s : Adjudicator E) (a : Address E) : Option (Outcome E) :=
  match a with
  | .external _ => none
  | .channel c => (s.statusOf c).finalizedWith s.now

/-- The mode of a channel at the chain's current time. -/
def Adjudicator.mode (s : Adjudicator E) (c : FixedPart) : Mode :=
  (s.statusOf c).mode s.now

variable [DecidableEq E]

/-- Nitro:395-398: "where the channel L itself has enough coins in the
    adjudicator to cover the entire allocation. In this case, we say the
    channel is directly funded." -/
def Adjudicator.DirectlyFunded (s : Adjudicator E) (c : FixedPart) : Prop :=
  ∃ o, s.finalOutcome c.address = some (.allocation o) ∧ o.total ≤ s.balances.get c.address

/-- Nitro:480-481 "directly funded with x coins": the channel holds `x`. -/
def Adjudicator.DirectlyFundedWith (s : Adjudicator E) (c : FixedPart) (x : Coins) : Prop :=
  x ≤ s.balances.get c.address

/-- The empty adjudicator. -/
def Adjudicator.genesis : Adjudicator E :=
  { balances := [], held := 0, status := [], now := 0 }

/-- go-nitro MultiAssetHolder.sol:38-63 `deposit(asset, channelId,
    expectedHeld, amount)`: "Deposit to external destination" reverts
    (line 43); `require(held == expectedHeld)` (line 51); then
    `held += amount`. The check is a compare-and-swap guard on the holding.
    Lines 45-49 give its reason: "1. Participant A deposits 2. Participant B
    sees A's deposit, which means it is now safe for them to deposit 3.
    Participant B submits their deposit 4. The chain re-orgs, leaving B's
    deposit in the chain but not A's." ForceMove:1197-1208 (§6.2 funding
    protocol): "It is only safe to [fund] in order". Nitro:165-168 `D_A(x)`;
    Nitro:227-228 allows either address kind, the code is followed: only a
    channel address. SATP:764-768 defers deposits.

    Reorganizations are not an operation. A
    history that drops or reorders earlier deposits is just another
    `Reachable` history; `expectedHeld` is what the depositor saw, and the
    guard fails when the chain no longer holds it. The model has no forks
    and no finality.

    Channel types (`ChannelKind`, SATP §1
    SATP:79-84, SATP §3.1): only a ledger channel accepts a deposit. A
    virtual channel is funded only by guarantees in ledger channels, never
    by a deposit of its own. -/
def Adjudicator.deposit (s : Adjudicator E) (a : Address E) (expectedHeld x : Coins) :
    Option (Adjudicator E) :=
  match a with
  | .channel c =>
    if c.kind = .ledger ∧ s.balances.get a = expectedHeld then
      some { s with balances := s.balances.add a x, held := s.held + x }
    else
      none
  | .external _ => none

/-- Pay `x` coins to a destination. go-nitro `_executeSingleAssetExit`
    (MultiAssetHolder.sol:402-415): an external destination receives the
    asset from the contract; a channel destination's holding rises. There
    is no withdrawal operation in go-nitro: Nitro:169-199 `W_A(x)` is
    realized by this payout, and SATP:764-768 defers withdrawals. -/
def Adjudicator.payTo (s : Adjudicator E) (b : Address E) (x : Coins) : Adjudicator E :=
  match b with
  | .external _ => { s with balances := s.balances.add b x, held := s.held - x }
  | .channel _ => { s with balances := s.balances.add b x }

/-- go-nitro MultiAssetHolder.sol:72-100 `transfer`: on a finalized channel,
    pay a selected allocation entry "as many funds escrowed against
    `channelId` as can be afforded" (line 66), in priority order
    (`compute_transfer_effects_and_interactions`, lines 162-191); a guarantee
    entry cannot be transferred (line 171-172). Nitro:765-772 `T(A, B, x)`
    with `x ≤` the affordable amount; the code pays the whole affordable
    amount, so `x` is not a parameter. SATP:764-768 defers payouts. The
    multi-index batch (`indices`) is an encoding and is not modelled.

    Channel types (`ChannelKind`, SATP §1
    SATP:79-84, SATP §3.1): only a ledger channel holds coins to pay out,
    so `a` must be one; a virtual channel source is never transferred
    from. The paid destination `b`, when it names a channel, must itself
    be a ledger channel (`Address.fundable`): a virtual channel never
    receives a credit from another channel's payout, because it holds no
    assets of its own. -/
def Adjudicator.transfer (s : Adjudicator E) (a : FixedPart) (b : Address E) :
    Option (Adjudicator E) :=
  if a.kind = .ledger ∧ b.fundable = true then
    match s.finalOutcome a.address with
    | some (.allocation o) =>
      match o.find b with
      | some ⟨_, .alloc _⟩ =>
        let x := o.paidTo (s.balances.get a.address) b
        some (((s.setStatus a ((s.statusOf a).withOutcome (.allocation (o.reduceOwed b x)))).payTo b x)
          |> fun s' => { s' with balances := s'.balances.sub a.address x })
      | _ => none
    | _ => none
  else none

/-- SATP:344-364 `reclaim(ledgerChannelId, targetChannelId)` (Listing 2) as
    corrected by go-nitro `reclaim` and `compute_reclaim_effects`
    (MultiAssetHolder.sol:233-370). The ledger is finalized. The ledger's
    entry for the target is a guarantee `G(x, [left, right])`. Then
    `o_ledger[left] += o_target[0]`, `o_ledger[right] += o_target[1]`, and
    the guarantee entry is deleted. go-nitro adds three checks SATP lacks:
    `left` and `right` must have entries in the ledger (lines 363-364) and
    `o_target[0] + o_target[1] = x` (line 365). The balances do not change
    (line 391: "no changes are made to the target channel"; the ledger's
    holding is untouched).

    Channel types (`ChannelKind`, SATP §1
    SATP:79-84, SATP §3.1): a guarantee names only a virtual channel as its
    target, so `reclaim` requires `v` to be one. The credit lands in the
    ledger's own allocation entries, SATP's "credits from another channel's
    payout", so `l` must be a ledger channel, as
    `transfer`'s paid channel destination must be.

    The target's finalized outcome (SATP §2.4
    SATP:335-338: "x tokens to be reclaimed, using the 'finalized' outcome
    of V"): `reclaim` reads `finalizedWith v.address`, the outcome `v`
    finalized with, not its current stored outcome. go-nitro reads the
    current stored outcome, and `transfer` can rewrite that outcome between
    finalization and a later `reclaim` call: a reclaim denial-of-service
    reproduced against go-nitro at `64c4ee9a1` (recorded in an internal defect note)
    into a finalized virtual channel, pays the deposit out by `transfer`,
    and every later `reclaim` then reverts forever on the amount check.
    With channel types a virtual channel accepts neither a deposit nor a
    transfer (`Adjudicator.deposit`, `Adjudicator.transfer`), so its stored
    outcome cannot move once finalized; reading `finalizedWith` states that
    fact directly, as SATP reads it, instead of leaving it to follow only
    from the deposit and transfer guards. -/
def Adjudicator.reclaim (s : Adjudicator E) (l v : FixedPart) : Option (Adjudicator E) :=
  if l.kind = .ledger ∧ v.kind = .virtual then
    match s.finalOutcome l.address, s.finalizedWith v.address with
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
  else none

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
def Adjudicator.challenge (apps : Apps E) (s : Adjudicator E) (challenger : Participant)
    (c : FixedPart) (proof : SupportProof E) (candidate : State E) : Option (Adjudicator E) :=
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
def Adjudicator.checkpoint (apps : Apps E) (s : Adjudicator E) (c : FixedPart)
    (proof : SupportProof E) (candidate : State E) : Option (Adjudicator E) :=
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
def Adjudicator.conclude (s : Adjudicator E) (c : FixedPart) (ss : SignedState E) :
    Option (Adjudicator E) :=
  if (s.statusOf c).IsOpen s.now ∧ ConclusionProof c ss then
    some (s.setStatus c (.finalized ss.state.turnNum ss.state.outcome ss.state.outcome))
  else
    none

/-- The chain clock moves forward. go-nitro reads `block.timestamp`;
    ForceMove:1261-1265: a challenge that receives no response "within the
    timeout period" terminates. -/
def Adjudicator.tick (s : Adjudicator E) (dt : Time) : Adjudicator E :=
  { s with now := s.now + dt }

/-- An on-chain operation. go-nitro NitroAdjudicator: `deposit`,
    `transfer`, `reclaim`, `challenge`, `checkpoint`, `conclude` (the batch
    helpers `transferAllAssets` and `concludeAndTransferAllAssets` are
    sequences of these). -/
inductive Op (E : Type)
  | deposit (a : Address E) (expectedHeld x : Coins)
  | transfer (a : FixedPart) (b : Address E)
  | reclaim (l v : FixedPart)
  | challenge (c : FixedPart) (proof : SupportProof E) (candidate : State E)
  | checkpoint (c : FixedPart) (proof : SupportProof E) (candidate : State E)
  | conclude (c : FixedPart) (ss : SignedState E)
  | tick (dt : Time)

/-- The signed states an operation submits. -/
def Op.proofStates : Op E → SupportProof E
  | .challenge _ proof _ => proof
  | .checkpoint _ proof _ => proof
  | .conclude _ ss => [ss]
  | _ => []

/-- Nitro:312-313: "There is no restriction on who can trigger the
    operations." go-nitro `transfer` and `reclaim` have no caller check. -/
def Op.isRedistribution : Op E → Bool
  | .transfer .. => true
  | .reclaim .. => true
  | _ => false

/-- Apply one operation by one caller. -/
def Adjudicator.apply (apps : Apps E) (caller : Participant) (op : Op E) (s : Adjudicator E) :
    Option (Adjudicator E) :=
  match op with
  | .deposit a e x => s.deposit a e x
  | .transfer a b => s.transfer a b
  | .reclaim l v => s.reclaim l v
  | .challenge c proof candidate => s.challenge apps caller c proof candidate
  | .checkpoint c proof candidate => s.checkpoint apps c proof candidate
  | .conclude c ss => s.conclude c ss
  | .tick dt => some (s.tick dt)

/-! ## One precondition and one effect per operation

Repair pass step R.2 (armada-laconic `docs/process.md`, "The repair pass"). Each `Op`
constructor has a decidable precondition `…Pre` and an effect `…Effect`. The effect takes
the argument that the precondition checks as a subtype value that carries the proof, so a
lemma about an effect needs no precondition hypothesis. `ArmadaLean/Nitro/OpEquations.lean`
states `apply` in the form `if h : Pre then some (Effect ⟨_, h⟩) else none`. The bodies are
the bodies of the operations above. `apply` does not change in this step.

The go-nitro line numbers are those of the go-nitro contracts as armada-nitro vendored them
unmodified, armada-nitro commit `8edacc10`, `src/nitro/`. -/

/-- The precondition of `deposit`. go-nitro MultiAssetHolder.sol:38-64 `deposit`: the
    destination is not external (line 44) and `held == expectedHeld` (lines 50-51). Only a
    ledger channel accepts a deposit (`ChannelKind`). A channel
    address is fundable exactly when it is a ledger channel (`Address.fundable`). -/
def Adjudicator.DepositPre (s : Adjudicator E) (a : Address E) (expectedHeld : Coins) : Prop :=
  a.isExternal = false ∧ a.fundable = true ∧ s.balances.get a = expectedHeld

instance (s : Adjudicator E) (a : Address E) (expectedHeld : Coins) :
    Decidable (s.DepositPre a expectedHeld) :=
  inferInstanceAs (Decidable (a.isExternal = false ∧ a.fundable = true ∧
    s.balances.get a = expectedHeld))

/-- The effect of `deposit`. go-nitro MultiAssetHolder.sol:38-64 `deposit`: the contract
    receives the coins (lines 54-58) and `held += amount` (lines 60-62). -/
def Adjudicator.depositEffect (s : Adjudicator E) (expectedHeld : Coins)
    (a : {a : Address E // s.DepositPre a expectedHeld}) (x : Coins) : Adjudicator E :=
  { s with balances := s.balances.add a.1 x, held := s.held + x }

/-- The allocation that `transfer` pays from: the finalized allocation of `a`, when its first
    entry for `b` is an `alloc` entry. go-nitro MultiAssetHolder.sol:75-110 `transfer` reads
    the outcome of a finalized channel (`_apply_transfer_checks`, lines 112-134), and
    `compute_transfer_effects_and_interactions` (lines 136-192) rejects a guarantee entry. -/
def Adjudicator.transferSource? (s : Adjudicator E) (a : FixedPart) (b : Address E) :
    Option (Allocation E) :=
  match s.finalOutcome a.address with
  | some (.allocation o) =>
    match o.find b with
    | some ⟨_, .alloc _⟩ => some o
    | _ => none
  | _ => none

/-- The precondition of `transfer`. go-nitro MultiAssetHolder.sol:75-110 `transfer`: the
    channel is finalized and the destination's entry is an `alloc` entry
    (`transferSource?`). Only a ledger channel pays out, and a channel destination is a
    ledger channel (`ChannelKind`). -/
def Adjudicator.TransferPre (s : Adjudicator E) (a : FixedPart) (b : Address E) : Prop :=
  a.kind = .ledger ∧ b.fundable = true ∧ (s.transferSource? a b).isSome = true

instance (s : Adjudicator E) (a : FixedPart) (b : Address E) : Decidable (s.TransferPre a b) :=
  inferInstanceAs (Decidable (a.kind = .ledger ∧ b.fundable = true ∧
    (s.transferSource? a b).isSome = true))

/-- The effect of `transfer`. go-nitro MultiAssetHolder.sol:75-110 `transfer`: pay `b` the
    amount that the holding of `a` affords (`compute_transfer_effects_and_interactions`,
    lines 136-192), reduce the holding of `a` and the entry of `b` in the stored outcome
    (`_apply_transfer_effects`, lines 204-209), and pay the destination
    (`_executeSingleAssetExit`, lines 405-416). -/
def Adjudicator.transferEffect (s : Adjudicator E) (b : Address E)
    (a : {a : FixedPart // s.TransferPre a b}) : Adjudicator E :=
  let o := (s.transferSource? a.1 b).get a.2.2.2
  let x := o.paidTo (s.balances.get a.1.address) b
  ((s.setStatus a.1 ((s.statusOf a.1).withOutcome (.allocation (o.reduceOwed b x)))).payTo b x)
    |> fun s' => { s' with balances := s'.balances.sub a.1.address x }

/-- The values that a `reclaim` reads: the ledger's finalized allocation, the target's
    finalized allocation, and the two destinations of the ledger's guarantee entry for the
    target. go-nitro MultiAssetHolder.sol:234-256 `reclaim`. -/
structure ReclaimSource (E : Type) where
  ledger : Allocation E
  target : Allocation E
  left : Address E
  right : Address E

/-- The values that `reclaim l v` reads, when every check passes. go-nitro
    MultiAssetHolder.sol:261-315 `_apply_reclaim_checks` and MultiAssetHolder.sol:320-369
    `compute_reclaim_effects`: both channels are finalized, the ledger's entry for the target
    is a guarantee with two destinations, each destination has an entry in the ledger, and
    the target's two amounts sum to the guarantee's amount. The target's outcome is the one
    it finalized with (`Adjudicator.reclaim`). -/
def Adjudicator.reclaimSource? (s : Adjudicator E) (l v : FixedPart) :
    Option (ReclaimSource E) :=
  match s.finalOutcome l.address, s.finalizedWith v.address with
  | some (.allocation oLedger), some (.allocation oTarget) =>
    match oLedger.find v.address with
    | some ⟨_, .guarantee x [left, right]⟩ =>
      if (oLedger.remove v.address).find left ≠ none ∧
          (oLedger.remove v.address).find right ≠ none ∧
          oTarget.amountAt 0 + oTarget.amountAt 1 = x then
        some ⟨oLedger, oTarget, left, right⟩
      else
        none
    | _ => none
  | _, _ => none

/-- The precondition of `reclaim`. go-nitro MultiAssetHolder.sol:234-256 `reclaim` and its
    checks (`reclaimSource?`). The ledger is a ledger channel and the target is a virtual
    channel (`ChannelKind`). -/
def Adjudicator.ReclaimPre (s : Adjudicator E) (l v : FixedPart) : Prop :=
  l.kind = .ledger ∧ v.kind = .virtual ∧ (s.reclaimSource? l v).isSome = true

instance (s : Adjudicator E) (l v : FixedPart) : Decidable (s.ReclaimPre l v) :=
  inferInstanceAs (Decidable (l.kind = .ledger ∧ v.kind = .virtual ∧
    (s.reclaimSource? l v).isSome = true))

/-- The effect of `reclaim`. go-nitro MultiAssetHolder.sol:320-369
    `compute_reclaim_effects` and MultiAssetHolder.sol:374-398 `_apply_reclaim_effects`:
    credit the target's two amounts to the two destinations in the ledger's allocation, and
    delete the guarantee entry. The balances do not change (line 397). -/
def Adjudicator.reclaimEffect (s : Adjudicator E) (v : FixedPart)
    (l : {l : FixedPart // s.ReclaimPre l v}) : Adjudicator E :=
  let r := (s.reclaimSource? l.1 v).get l.2.2.2
  let o1 := r.ledger.addTo r.left (r.target.amountAt 0)
  let o2 := o1.addTo r.right (r.target.amountAt 1)
  s.setStatus l.1 ((s.statusOf l.1).withOutcome (.allocation (o2.remove v.address)))

/-- The precondition of `challenge`. go-nitro ForceMove.sol:39-81 `challenge`: the candidate's
    turn does not decrease the record in Open mode and increases it in Challenge mode
    (lines 48-55), the proof supports the candidate (lines 57-60), and the challenger is a
    participant (line 63). -/
def Adjudicator.ChallengePre (apps : Apps E) (s : Adjudicator E) (challenger : Participant)
    (c : FixedPart) (proof : SupportProof E) (candidate : State E) : Prop :=
  challenger ∈ c.participants ∧
    (apps c.appDef).supports c proof candidate = true ∧ candidate.channel = c ∧
    ((s.mode c = .open ∧ (s.statusOf c).turnNumRecord ≤ candidate.turnNum) ∨
     (s.mode c = .challenge ∧ (s.statusOf c).turnNumRecord < candidate.turnNum))

instance (apps : Apps E) (s : Adjudicator E) (challenger : Participant) (c : FixedPart)
    (proof : SupportProof E) (candidate : State E) :
    Decidable (s.ChallengePre apps challenger c proof candidate) :=
  inferInstanceAs (Decidable (challenger ∈ c.participants ∧
    (apps c.appDef).supports c proof candidate = true ∧ candidate.channel = c ∧
    ((s.mode c = .open ∧ (s.statusOf c).turnNumRecord ≤ candidate.turnNum) ∨
     (s.mode c = .challenge ∧ (s.statusOf c).turnNumRecord < candidate.turnNum))))

/-- The effect of `challenge`. go-nitro ForceMove.sol:39-81 `challenge`: the status becomes
    the candidate's turn and `block.timestamp + challengeDuration` (lines 73-80). -/
def Adjudicator.challengeEffect (apps : Apps E) (s : Adjudicator E) (challenger : Participant)
    (c : FixedPart) (proof : SupportProof E)
    (candidate : {st : State E // s.ChallengePre apps challenger c proof st}) : Adjudicator E :=
  s.setStatus c (.challenged candidate.1.turnNum ⟨candidate.1, s.now + c.challengeDuration⟩)

/-- The precondition of `checkpoint`. go-nitro ForceMove.sol:90-119 `checkpoint`: the channel
    is not finalized (line 99), the candidate's turn increases the record (line 100), and the
    proof supports the candidate (lines 101-104). -/
def Adjudicator.CheckpointPre (apps : Apps E) (s : Adjudicator E) (c : FixedPart)
    (proof : SupportProof E) (candidate : State E) : Prop :=
  (s.statusOf c).IsOpen s.now ∧
    (apps c.appDef).supports c proof candidate = true ∧ candidate.channel = c ∧
    (s.statusOf c).turnNumRecord < candidate.turnNum

instance (apps : Apps E) (s : Adjudicator E) (c : FixedPart) (proof : SupportProof E)
    (candidate : State E) : Decidable (s.CheckpointPre apps c proof candidate) :=
  inferInstanceAs (Decidable ((s.statusOf c).IsOpen s.now ∧
    (apps c.appDef).supports c proof candidate = true ∧ candidate.channel = c ∧
    (s.statusOf c).turnNumRecord < candidate.turnNum))

/-- The effect of `checkpoint`. go-nitro ForceMove.sol:90-119 `checkpoint`: the status
    becomes Open at the candidate's turn, and a running challenge is cleared
    (lines 108-111). -/
def Adjudicator.checkpointEffect (apps : Apps E) (s : Adjudicator E) (c : FixedPart)
    (proof : SupportProof E) (candidate : {st : State E // s.CheckpointPre apps c proof st}) :
    Adjudicator E :=
  s.setStatus c (.open candidate.1.turnNum)

/-- The precondition of `conclude`. go-nitro ForceMove.sol:127-132 `conclude` and
    ForceMove.sol:140-170 `_conclude`: the channel is not finalized (line 147), the candidate
    is final (line 148), and every participant signed it (lines 149-157). -/
def Adjudicator.ConcludePre (s : Adjudicator E) (c : FixedPart) (ss : SignedState E) : Prop :=
  (s.statusOf c).IsOpen s.now ∧ ConclusionProof c ss

instance (s : Adjudicator E) (c : FixedPart) (ss : SignedState E) :
    Decidable (s.ConcludePre c ss) :=
  inferInstanceAs (Decidable ((s.statusOf c).IsOpen s.now ∧ ConclusionProof c ss))

/-- The effect of `conclude`. go-nitro ForceMove.sol:140-170 `_conclude`: the channel
    finalizes at once with the candidate's outcome (lines 160-167). The model keeps the
    candidate's turn (`Adjudicator.conclude`). -/
def Adjudicator.concludeEffect (s : Adjudicator E) (c : FixedPart)
    (ss : {ss : SignedState E // s.ConcludePre c ss}) : Adjudicator E :=
  s.setStatus c (.finalized ss.1.state.turnNum ss.1.state.outcome ss.1.state.outcome)

/-- The precondition of `tick`: the clock does not move backward. go-nitro reads
    `block.timestamp` (StatusManager.sol:17-30 `_mode`, line 25). No contract call moves the
    clock and no contract check can stop it, so the precondition holds for every `dt`
    (`Time` is `Nat`). -/
def Adjudicator.TickPre (s : Adjudicator E) (dt : Time) : Prop := s.now ≤ s.now + dt

instance (s : Adjudicator E) (dt : Time) : Decidable (s.TickPre dt) :=
  inferInstanceAs (Decidable (s.now ≤ s.now + dt))

/-- The effect of `tick`: the chain clock moves forward by `dt`. go-nitro
    StatusManager.sol:17-30 `_mode` compares `finalizesAt` with `block.timestamp`
    (line 25). -/
def Adjudicator.tickEffect (s : Adjudicator E) (dt : {dt : Time // s.TickPre dt}) :
    Adjudicator E :=
  { s with now := s.now + dt.1 }

/-- One successful on-chain step. -/
inductive Step (apps : Apps E) : Adjudicator E → Adjudicator E → Prop
  | mk (caller : Participant) (op : Op E) (s s' : Adjudicator E)
      (h : s.apply apps caller op = some s') : Step apps s s'

/-- The states reachable from genesis: the reflexive transitive closure of
    `Step` (Mathlib `Relation.ReflTransGen`). -/
def Reachable (apps : Apps E) (s : Adjudicator E) : Prop :=
  Relation.ReflTransGen (Step apps) Adjudicator.genesis s

/-- The signatures that exist: `(q, st) ∈ signed` when `q` signed `st`. A
    proof state is genuine when each listed signer signed it, and each
    signer listed in its voucher signed a state that carries the voucher
    (SATP:703 `voucherSignedByAll`). Symbolic signatures are data
    (`Channel.lean`); this predicate says which of them a history may use. -/
def SignedState.SignedIn (signed : List (Participant × State E)) (ss : SignedState E) : Prop :=
  (∀ q ∈ ss.signers, (q, ss.state) ∈ signed) ∧
  ∀ v, ss.state.voucher? = some v → ∀ q ∈ v.signers, ∃ st, (q, st) ∈ signed ∧ st.voucher? = some v

/-- One successful on-chain step whose proof states are all genuine for
    `signed`. -/
inductive SignedStep (apps : Apps E) (signed : List (Participant × State E)) :
    Adjudicator E → Adjudicator E → Prop
  | mk (caller : Participant) (op : Op E) (s s' : Adjudicator E)
      (hsig : ∀ ss ∈ op.proofStates, ss.SignedIn signed)
      (h : s.apply apps caller op = some s') : SignedStep apps signed s s'

/-- The states reachable from genesis by steps that use only the signatures
    in `signed` (Mathlib `Relation.ReflTransGen`). SATP:168: forging a
    signature is infeasible. -/
def ReachableSigned (apps : Apps E) (signed : List (Participant × State E)) (s : Adjudicator E) :
    Prop :=
  Relation.ReflTransGen (SignedStep apps signed) Adjudicator.genesis s

/-- Apply a list of (caller, op) pairs. A failed operation changes nothing
    and the sequence continues. -/
def Adjudicator.applyAll (apps : Apps E) : List (Participant × Op E) → Adjudicator E → Adjudicator E
  | [], s => s
  | (caller, op) :: rest, s => Adjudicator.applyAll apps rest ((s.apply apps caller op).getD s)

end ArmadaLean.Nitro
