/-
  Nitro protocol specification: the SATP virtual channel rules (SATP Appendix
  A, lines 608-757) and Protocols 3.1-3.3 (SATP:407-485). See `Address.lean`
  for the source list.

  App data (operator ruling 2026-10-27, choice 5). SATP:209 says `appData` is
  "parsed by custom app logic". Here the state carries the parsed value
  `VirtualAppData` directly (`State.appData`, `Channel.lean`); there is no
  byte string and no decoder. ABI encoding and decoding, and the round-trip
  theorem `(encode v) = some v`, belong to the refinement layer, not
  to this branch.

  Destinations (operator ruling 2026-10-27). SATP:710-717 writes the voucher
  outcome as `{alice : v.alice, bob : v.bob}`, with the peers' keys as
  destinations. Here destinations are external destinations, not
  participants, so the voucher outcome pays the first two destinations of the
  start state's outcome, in order (SATP:705 reads the same two entries).

  go-nitro `VirtualPaymentApp.sol` is a different application: one-way
  vouchers from Alice to Bob, redeemed by Bob at turn 2 with the post-fund
  state as proof, and no response state. SATP:444-449 names that
  unidirectional case. The paper's two-way rules (Listing 3) are what Lemma
  3.1 and Theorem 3.2 rest on, so the paper is followed here; the code's app
  is a special case, not a correction.
-/
import ArmadaLean.Nitro.Constructions

namespace ArmadaLean.Nitro

variable {E : Type} [DecidableEq E]

/-- SATP:703 `voucherSignedByAll(voucher, [alice, bob])`. -/
def Voucher.SignedByBoth (v : Voucher) (alice bob : Participant) : Prop :=
  alice ∈ v.signers ∧ bob ∈ v.signers

/-- SATP:710-717, SATP:735-738: the outcome `{alice : v.alice, bob : v.bob}`,
    paid to the destinations `da` and `db`. -/
def Voucher.outcome (v : Voucher) (da db : Address E) : Outcome E :=
  .allocation [⟨da, .alloc v.alice⟩, ⟨db, .alloc v.bob⟩]

/-- SATP:705 `x = start.outcome[0].amount + start.outcome[1].amount`. -/
def Outcome.fundedTotal : Outcome E → Coins
  | .allocation o => o.amountAt 0 + o.amountAt 1

/-- The destinations of the first two entries of an outcome. -/
def Outcome.pairDests : Outcome E → Option (Address E × Address E)
  | .allocation (e0 :: e1 :: _) => some (e0.dest, e1.dest)
  | _ => none

/-- SATP:682-690: the start state. -/
def validStart (c : FixedPart) (s : SignedState E) : Bool :=
  match s.state.appData with
  | .satpVirtual d => decide (d.type = .none) && decide s.ByAll && decide (s.state.channel = c)
  | .opaque _ => false

/-- SATP:691-720: a challenge state after the start state. -/
def validChallenge (c : FixedPart) (alice bob : Participant) (s ch : SignedState E) : Bool :=
  match ch.state.appData, s.state.outcome.pairDests with
  | .satpVirtual d, some (da, db) =>
    validStart c s && decide (s.state.turnNum = 1) && decide (ch.state.turnNum = 2) &&
    decide (ch.state.channel = c) &&
    ((decide (d.type = .A) && decide (alice ∈ ch.signers)) ||
      (decide (d.type = .B) && decide (bob ∈ ch.signers))) &&
    decide (alice ∈ d.voucher.signers) && decide (bob ∈ d.voucher.signers) &&
    decide (d.voucher.alice + d.voucher.bob = s.state.outcome.fundedTotal) &&
    decide (ch.state.outcome = d.voucher.outcome da db)
  | _, _ => false

/-- SATP:722-740: a response state after a challenge state. -/
def validResponse (c : FixedPart) (alice bob : Participant) (s ch re : SignedState E) : Bool :=
  match ch.state.appData, re.state.appData, s.state.outcome.pairDests with
  | .satpVirtual dc, .satpVirtual dr, some (da, db) =>
    validChallenge c alice bob s ch && decide (re.state.turnNum = 3) &&
    decide (re.state.channel = c) && decide (dr.type = .AB) &&
    (!decide (dc.type = .A) || decide (bob ∈ re.signers)) &&
    (!decide (dc.type = .B) || decide (alice ∈ re.signers)) &&
    decide (alice ∈ dr.voucher.signers) && decide (bob ∈ dr.voucher.signers) &&
    decide (dc.voucher.version < dr.voucher.version) &&
    decide (dr.voucher.alice + dr.voucher.bob = s.state.outcome.fundedTotal) &&
    decide (re.state.outcome = dr.voucher.outcome da db)
  | _, _, _ => false

/-- SATP:669-741 `validateOutcomeChange` (Listing 3). `alice = peers[0]`,
    `bob = peers.at(-1)` (SATP:679-680). `proof` is the start state, the
    start and a challenge, or the start, a challenge and a response;
    `candidate` is the last of them. -/
def validateOutcomeChange (c : FixedPart) (alice bob : Participant) :
    SupportProof E → State E → Bool
  | [s], candidate => validStart c s && decide (s.state = candidate)
  | [s, ch], candidate => validChallenge c alice bob s ch && decide (ch.state = candidate)
  | [s, ch, re], candidate =>
    validResponse c alice bob s ch re && decide (re.state = candidate)
  | _, _ => false

/-- SATP:644-667 `latestSupportedState` of the virtual channel app: version
    `≤ 1` needs consensus (pre-fund 0, post-fund 1); version `4` needs
    consensus and `isFinal`; otherwise `validateOutcomeChange`. The result is
    the last state received. -/
def satpVirtualRules : Rules E where
  supports c proof candidate :=
    match c.participants.head?, c.participants.getLast? with
    | some alice, some bob =>
      if candidate.turnNum ≤ 1 then consensusRules.supports c proof candidate
      else if candidate.turnNum = 4 then
        consensusRules.supports c proof candidate && candidate.isFinal
      else validateOutcomeChange c alice bob proof candidate
    | _, _ => false

/-- SATP:408-409: the pre-fund outcome `{A : A(a0), B : A(b0)}`, paid to the
    destinations `da` of Alice and `db` of Bob. -/
def originalOutcome (da db : E) (a0 b0 : Coins) : Outcome E :=
  .allocation [alloc (.external da) a0, alloc (.external db) b0]

/-- SATP:511-513: an outcome `{A : A(a), B : A(b)}`. -/
def PairOutcome (da db : E) (Ω : Outcome E) (a b : Coins) : Prop :=
  Ω = .allocation [alloc (.external da) a, alloc (.external db) b]

/-- SATP:400-404: peers `Alice = P0, P1, ..., Pn, Pn+1 = Bob`; for each `i` a
    ledger channel `Li` between `Pi` and `Pi+1` running the consensus app;
    the virtual channel `V` between Alice and Bob with pre-fund amounts
    `a0`, `b0`. `dest P` is the external destination of peer `P`. -/
structure Route (E : Type) where
  peers : List Participant
  ledgers : List FixedPart
  V : FixedPart
  a0 : Coins
  b0 : Coins
  dest : Participant → E

/-- SATP:400-402 and SATP:679-680: the ledgers link consecutive peers and run the
    consensus app; `V`'s peers are the route; the peers' destinations are
    distinct. -/
def Route.WellFormed (apps : Apps E) (r : Route E) : Prop :=
  r.ledgers.length + 1 = r.peers.length ∧ 2 ≤ r.peers.length ∧ r.peers.Nodup ∧
  (r.peers.map r.dest).Nodup ∧
  (∀ (i : Nat) L, r.ledgers[i]? = some L → ∃ P Q, r.peers[i]? = some P ∧ r.peers[i + 1]? = some Q ∧
    L.participants = [P, Q] ∧ IsLedgerChannel apps L) ∧
  r.V.participants = r.peers ∧
  (∀ (i : Nat) L, r.ledgers[i]? = some L → L ≠ r.V)

/-- SATP:413 `Gi = V : G(a0 + b0, [Pi, Pi+1])`. -/
def Route.guarantee (r : Route E) (P Q : Participant) : Entry E :=
  ⟨r.V.address, .guarantee (r.a0 + r.b0) [.external (r.dest P), .external (r.dest Q)]⟩

/-- SATP:436-439: "each Pi has x = a0 + b0 fewer tokens across their two
    ledger channels"; "Alice (P0) has a0 fewer tokens in L0"; "Bob (Pn+1)
    has b0 fewer tokens in Ln". This is `d(V, Pi)` of SATP:503-504. -/
def Route.debited (r : Route E) (i : Nat) : Coins :=
  (if i = 0 then 0 else r.b0) + (if i + 1 = r.peers.length then 0 else r.a0)

/-- A ledger outcome after Round 2 of Protocol 3.1 (SATP:411-418): `P`'s entry
    fell by `debit` from `bal`, both peers have entries (go-nitro `reclaim`
    needs them, MultiAssetHolder.sol:363-364), and the guarantee
    `G(a0 + b0, [P, Q])` for `V` is present. -/
def Route.LedgerAfterRound2 (r : Route E) (o : Allocation E) (P Q : Participant)
    (bal debit : Coins) : Prop :=
  o.owed (.external (r.dest P)) + debit = bal ∧ o.find (.external (r.dest P)) ≠ none ∧
  o.find (.external (r.dest Q)) ≠ none ∧ o.find r.V.address = some (r.guarantee P Q)

/-- A ledger outcome before Round 2: `P` is owed `bal` and no entry targets
    `V`. -/
def Route.LedgerBeforeRound2 (r : Route E) (o : Allocation E) (P : Participant) (bal : Coins) :
    Prop :=
  o.owed (.external (r.dest P)) = bal ∧ o.find r.V.address = none

/-- `P` holds a consensus support for the state of `L` with outcome `o`, and
    every other state of `L` that `P` signed has a lower turn (SATP:398-399
    "blocking"; SATP:545-547 "these supported states have a greater version
    number than any other supported states held by anyone"). "Anyone"
    includes the chain: its record of `L` is below that turn, or is that
    state. `P` signed no final state of `L`: a final state finalizes the
    ledger at once (SATP:286-289), so a ledger that is still in use has
    none. -/
def HoldsLatestLedger {P : Participant} (net : NetworkState E P) (L : FixedPart) (o : Allocation E) :
    Prop :=
  ∃ ss, net.Holds ss ∧ ss.ByAll ∧ ss.state.channel = L ∧
    ss.state.outcome = .allocation o ∧ ss.state.isFinal = false ∧
    (∀ t ∈ net.sent, t.state.channel = L →
      (t.state.turnNum < ss.state.turnNum ∨ t.state = ss.state) ∧ t.state.isFinal = false) ∧
    ((∃ t, net.chain.statusOf L = .open t ∧ t ≤ ss.state.turnNum) ∨
     (∃ t ch, net.chain.statusOf L = .challenged t ch ∧
       (t < ss.state.turnNum ∨ ch.state = ss.state)))

/-- `P` committed `V`'s pre-fund state (version 0, SATP:408-409) and at most
    the post-fund state (version 1, SATP:420-421), and nothing else in `V`. -/
def HoldsVirtualSetup {P : Participant} (net : NetworkState E P) (r : Route E)
    (alice bob : Participant) (postFund : Bool) : Prop :=
  (∀ t ∈ net.sent, t.state.channel = r.V →
    t.state.outcome = originalOutcome (r.dest alice) (r.dest bob) r.a0 r.b0 ∧
    t.state.isFinal = false ∧
    (t.state.turnNum = 0 ∨ (postFund = true ∧ t.state.turnNum = 1))) ∧
  (∃ t ∈ net.sent, t.state.channel = r.V ∧ t.state.turnNum = 0)

/-- The goal of Theorem 3.2 for `Pi` with ledgers `Lm = L_{i-1}` and
    `Lp = L_i`: both are finalized with allocations, no entry targets `V`,
    and `Pi` is owed its pre-protocol balances `balm + balp` in total.
    SATP:498-500: "intermediaries' balances are invariant and are not locked up
    indefinitely in the virtual channel." The owed amounts are read in the
    stored outcomes, after any reclaim. A payout moves an owed amount to the
    balance of `Pi`'s destination, so the goal counts that balance above
    `base`, the balance when the strategy starts. -/
def IntermediaryRecovered {P : Participant} (r : Route E) (Lm Lp : FixedPart) (balm balp : Coins)
    (base : Coins) (net : NetworkState E P) : Prop :=
  ∃ om op, net.chain.finalOutcome Lm.address = some (.allocation om) ∧
    net.chain.finalOutcome Lp.address = some (.allocation op) ∧
    om.find r.V.address = none ∧ op.find r.V.address = none ∧
    balm + balp + base ≤
      om.owed (.external (r.dest P)) + op.owed (.external (r.dest P)) +
        net.chain.balances.get (.external (r.dest P))

/-- The goal for an end user (Alice, `L₀`): the ledger is finalized with no
    entry for `V` and Alice is owed her pre-protocol balance minus `a0` plus
    her share `a` of `V`'s final outcome, in the stored outcome, counting her
    destination's balance above `base` as in `IntermediaryRecovered`. -/
def EndUserRecovered {P : Participant} (r : Route E) (L : FixedPart) (bal : Coins)
    (share base : Coins) (net : NetworkState E P) : Prop :=
  ∃ o, net.chain.finalOutcome L.address = some (.allocation o) ∧ o.find r.V.address = none ∧
    bal + share + base ≤
      o.owed (.external (r.dest P)) + r.a0 + net.chain.balances.get (.external (r.dest P))

end ArmadaLean.Nitro
