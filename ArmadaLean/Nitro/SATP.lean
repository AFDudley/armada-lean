/-
  Nitro protocol specification: the SATP virtual channel rules (SATP Appendix
  A, lines 608-757) and Protocols 3.1-3.3 (SATP:407-485). See `Address.lean`
  for the source list.

  Modelling choice (app data). SATP:209 says `appData` is "parsed by custom
  app logic". The virtual channel rules read a state type and a voucher from
  it. `Decode` is that parse, a parameter of the rules.

  go-nitro `VirtualPaymentApp.sol` is a different application: one-way
  vouchers from Alice to Bob, redeemed by Bob at turn 2 with the post-fund
  state as proof, and no response state. SATP:444-449 names that
  unidirectional case. The paper's two-way rules (Listing 3) are what Lemma
  3.1 and Theorem 3.2 rest on, so the paper is followed here; the code's app
  is a special case, not a correction.
-/
import ArmadaLean.Nitro.Constructions

namespace ArmadaLean.Nitro

/-- SATP:630-637 `Voucher { virtualChannelId, version, alice, bob,
    signatures }`. -/
structure Voucher where
  virtualChannelId : FixedPart
  version : Nat
  alice : Coins
  bob : Coins
  signers : List Participant
  deriving DecidableEq, Repr

/-- SATP:616-620: "The setup states are given type None. Alice can move from a
    state with type None to a state with type A, or a state with type B to a
    state with type AB. Bob can move from ... None to ... B, or ... A to
    AB." -/
inductive VType
  | none
  | A
  | B
  | AB
  deriving DecidableEq, Repr

/-- The app data of a virtual channel state: its type and its voucher. -/
structure VirtualAppData where
  type : VType
  voucher : Voucher
  deriving Repr

/-- The parse of `State.appData` (SATP:209). -/
abbrev Decode := Nat → VirtualAppData

/-- SATP:703 `voucherSignedByAll(voucher, [alice, bob])`. -/
def Voucher.SignedByBoth (v : Voucher) (alice bob : Participant) : Prop :=
  alice ∈ v.signers ∧ bob ∈ v.signers

/-- SATP:710-717, SATP:735-738: the outcome `{alice : v.alice, bob : v.bob}`. -/
def Voucher.outcome (v : Voucher) (alice bob : Participant) : Outcome :=
  .allocation [alloc alice.address v.alice, alloc bob.address v.bob]

/-- SATP:705 `x = start.outcome[0].amount + start.outcome[1].amount`. -/
def Outcome.fundedTotal : Outcome → Coins
  | .allocation o => o.amountAt 0 + o.amountAt 1

/-- SATP:669-741 `validateOutcomeChange` (Listing 3). `alice = peers[0]`,
    `bob = peers.at(-1)` (SATP:679-680). The relation holds when `proof` is
    the start state, the start and a challenge, or the start, a challenge
    and a response, and `candidate` is the last of them. -/
inductive ValidateOutcomeChange (decode : Decode) (c : FixedPart) (alice bob : Participant) :
    SupportProof → State → Prop
  /-- SATP:682-690: only the start state. -/
  | start (s : SignedState) :
      (decode s.state.appData).type = .none → s.ByAll → s.state.channel = c →
      ValidateOutcomeChange decode c alice bob [s] s.state
  /-- SATP:691-720: start and challenge. -/
  | challenge (s ch : SignedState) :
      (decode s.state.appData).type = .none → s.ByAll → s.state.channel = c →
      s.state.turnNum = 1 → ch.state.turnNum = 2 → ch.state.channel = c →
      ((decode ch.state.appData).type = .A ∧ alice ∈ ch.signers ∨
        (decode ch.state.appData).type = .B ∧ bob ∈ ch.signers) →
      (decode ch.state.appData).voucher.SignedByBoth alice bob →
      (decode ch.state.appData).voucher.alice + (decode ch.state.appData).voucher.bob =
        s.state.outcome.fundedTotal →
      ch.state.outcome = (decode ch.state.appData).voucher.outcome alice bob →
      ValidateOutcomeChange decode c alice bob [s, ch] ch.state
  /-- SATP:722-740: start, challenge and response. -/
  | response (s ch re : SignedState) :
      ValidateOutcomeChange decode c alice bob [s, ch] ch.state →
      re.state.turnNum = 3 → re.state.channel = c →
      (decode re.state.appData).type = .AB →
      ((decode ch.state.appData).type = .A → bob ∈ re.signers) →
      ((decode ch.state.appData).type = .B → alice ∈ re.signers) →
      (decode re.state.appData).voucher.SignedByBoth alice bob →
      (decode ch.state.appData).voucher.version < (decode re.state.appData).voucher.version →
      (decode re.state.appData).voucher.alice + (decode re.state.appData).voucher.bob =
        s.state.outcome.fundedTotal →
      re.state.outcome = (decode re.state.appData).voucher.outcome alice bob →
      ValidateOutcomeChange decode c alice bob [s, ch, re] re.state

/-- SATP:644-667 `latestSupportedState` of the virtual channel app: version
    `≤ 1` needs consensus (pre-fund 0, post-fund 1); version `4` needs
    consensus and `isFinal`; otherwise `validateOutcomeChange`. The result is
    the last state received. -/
def satpVirtualRules (decode : Decode) : Rules where
  supports c proof candidate :=
    ∃ alice bob, c.participants.head? = some alice ∧ c.participants.getLast? = some bob ∧
    ((candidate.turnNum ≤ 1 ∧ consensusRules.supports c proof candidate) ∨
     (candidate.turnNum = 4 ∧ consensusRules.supports c proof candidate ∧
        candidate.isFinal = true) ∨
     (1 < candidate.turnNum ∧ candidate.turnNum ≠ 4 ∧
        ValidateOutcomeChange decode c alice bob proof candidate))

/-- SATP:408-409: the pre-fund outcome `{A : A(a0), B : A(b0)}`. -/
def originalOutcome (alice bob : Participant) (a0 b0 : Coins) : Outcome :=
  .allocation [alloc alice.address a0, alloc bob.address b0]

/-- SATP:511-513: an outcome `{A : A(a), B : A(b)}`. -/
def PairOutcome (alice bob : Participant) (Ω : Outcome) (a b : Coins) : Prop :=
  Ω = .allocation [alloc alice.address a, alloc bob.address b]

/-- SATP:400-404: peers `Alice = P0, P1, ..., Pn, Pn+1 = Bob`; for each `i` a
    ledger channel `Li` between `Pi` and `Pi+1` running the consensus app;
    the virtual channel `V` between Alice and Bob with pre-fund amounts
    `a0`, `b0`. -/
structure Route where
  peers : List Participant
  ledgers : List FixedPart
  V : FixedPart
  a0 : Coins
  b0 : Coins

/-- SATP:400-402 and SATP:679-680: the ledgers link consecutive peers and run the
    consensus app; `V`'s peers are the route. -/
def Route.WellFormed (apps : Apps) (r : Route) : Prop :=
  r.ledgers.length + 1 = r.peers.length ∧ 2 ≤ r.peers.length ∧ r.peers.Nodup ∧
  (∀ (i : Nat) L, r.ledgers[i]? = some L → ∃ P Q, r.peers[i]? = some P ∧ r.peers[i + 1]? = some Q ∧
    L.participants = [P, Q] ∧ IsLedgerChannel apps L) ∧
  r.V.participants = r.peers ∧
  (∀ (i : Nat) L, r.ledgers[i]? = some L → L ≠ r.V)

/-- SATP:413 `Gi = V : G(a0 + b0, [Pi, Pi+1])`. -/
def Route.guarantee (r : Route) (P Q : Participant) : Entry :=
  ⟨r.V.address, .guarantee (r.a0 + r.b0) [P.address, Q.address]⟩

/-- SATP:436-439: "each Pi has x = a0 + b0 fewer tokens across their two
    ledger channels"; "Alice (P0) has a0 fewer tokens in L0"; "Bob (Pn+1)
    has b0 fewer tokens in Ln". This is `d(V, Pi)` of SATP:503-504. -/
def Route.debited (r : Route) (i : Nat) : Coins :=
  (if i = 0 then 0 else r.b0) + (if i + 1 = r.peers.length then 0 else r.a0)

/-- A ledger outcome after Round 2 of Protocol 3.1 (SATP:411-418): `P`'s entry
    fell by `debit` from `bal`, both peers have entries (go-nitro `reclaim`
    needs them, MultiAssetHolder.sol:363-364), and the guarantee
    `G(a0 + b0, [P, Q])` for `V` is present. -/
def Route.LedgerAfterRound2 (r : Route) (o : Allocation) (P Q : Participant) (bal debit : Coins) :
    Prop :=
  o.owed P.address + debit = bal ∧ o.find P.address ≠ none ∧ o.find Q.address ≠ none ∧
  o.find r.V.address = some (r.guarantee P Q)

/-- A ledger outcome before Round 2: `P` is owed `bal` and no entry targets
    `V`. -/
def Route.LedgerBeforeRound2 (r : Route) (o : Allocation) (P : Participant) (bal : Coins) : Prop :=
  o.owed P.address = bal ∧ o.find r.V.address = none

/-- `P` holds a consensus support for the state of `L` with outcome `o`, and
    `P` signed no higher state of `L` (SATP:398-399 "blocking"; SATP:545-547
    "these supported states have a greater version number than any other
    supported states held by anyone"). -/
def HoldsLatestLedger {P : Participant} (net : NetworkState P) (L : FixedPart) (o : Allocation) :
    Prop :=
  ∃ ss, net.Holds ss ∧ ss.ByAll ∧ ss.state.channel = L ∧
    ss.state.outcome = .allocation o ∧ ss.state.isFinal = false ∧
    ∀ t ∈ net.sent, t.state.channel = L → t.state.turnNum ≤ ss.state.turnNum

/-- `P` committed `V`'s pre-fund state (version 0, SATP:408-409) and at most
    the post-fund state (version 1, SATP:420-421), and nothing else in `V`. -/
def HoldsVirtualSetup {P : Participant} (net : NetworkState P) (r : Route) (alice bob : Participant)
    (postFund : Bool) : Prop :=
  (∀ t ∈ net.sent, t.state.channel = r.V →
    t.state.outcome = originalOutcome alice bob r.a0 r.b0 ∧ t.state.isFinal = false ∧
    (t.state.turnNum = 0 ∨ (postFund = true ∧ t.state.turnNum = 1))) ∧
  (∃ t ∈ net.sent, t.state.channel = r.V ∧ t.state.turnNum = 0)

/-- The goal of Theorem 3.2 for `Pi` with ledgers `Lm = L_{i-1}` and
    `Lp = L_i`: both are finalized with allocations, no entry targets `V`,
    and `Pi` is owed its pre-protocol balances `balm + balp` in total.
    SATP:498-500: "intermediaries' balances are invariant and are not locked up
    indefinitely in the virtual channel." -/
def IntermediaryRecovered {P : Participant} (r : Route) (Lm Lp : FixedPart) (balm balp : Coins)
    (net : NetworkState P) : Prop :=
  ∃ om op, net.Finalized Lm (.allocation om) ∧ net.Finalized Lp (.allocation op) ∧
    om.find r.V.address = none ∧ op.find r.V.address = none ∧
    om.owed P.address + op.owed P.address = balm + balp

/-- The goal for an end user (Alice, `L₀`): the ledger is finalized with no
    entry for `V` and Alice is owed her pre-protocol balance minus `a0` plus
    her share `a` of `V`'s final outcome. -/
def EndUserRecovered {P : Participant} (r : Route) (L : FixedPart) (bal : Coins)
    (share : Coins) (net : NetworkState P) : Prop :=
  ∃ o, net.Finalized L (.allocation o) ∧ o.find r.V.address = none ∧
    o.owed P.address + r.a0 = bal + share

end ArmadaLean.Nitro
