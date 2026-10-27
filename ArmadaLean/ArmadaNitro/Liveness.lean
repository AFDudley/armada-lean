/-
  Armada adjudicator: liveness theorems at note level. Each theorem is the
  Armada form of a Nitro or SATP liveness theorem (`ArmadaLean/Nitro/
  Liveness.lean`). A Nitro balance increase of participant `p` is here a
  payment note keyed to `p`'s payee key (`Holder.paid`, ruling 4); a channel
  balance is the total of the channel's notes (ruling 2).

  The pool is an assumption of these theorems, through `PoolExecutes`
  (Notes.lean): the deployed pool executes an owned spend only within its
  circuit shapes and range check (open design choice D1).

  In the game theorems an honest call carries the notes it spends, so a
  concurrent call can make it stale. The Nitro proofs do not cover that. The
  Armada proofs rest on `pending_payout_not_blocked` (Safety.lean): on a
  finalized channel, only a payout or a reclaim on that channel, or a credit
  while the entry is underfunded, makes a pending payout stale. Each such
  call pays a positive amount or removes a guarantee entry, so an adversary
  can make a pending payout stale only a finite number of times. A transfer
  that affords nothing spends no note (`ArmadaStep.transferZero`); without
  that rule the adversary could repeat it forever (finding F3).

  Every theorem has proof `sorry`; the statements are the deliverable.
-/
import ArmadaLean.ArmadaNitro.Safety
import ArmadaLean.ArmadaNitro.Strategy

namespace ArmadaLean.ArmadaNitro

set_option autoImplicit false

open ArmadaLean.Nitro (Coins Participant FixedPart Address Allocation Apps Route alloc
  Concluded HoldsLatestLedger HoldsVirtualSetup originalOutcome satpVirtualRules IsLedgerChannel)

variable {cfg : Config} {apps : Apps}

/-- The payout of `x` to `b` exists as a note in token `t`: for a participant,
    a live payment note with its payee key and value `x`; for a channel, a live
    channel note keyed to the adjudicator with value `x`. -/
def PaidNote (cfg : Config) (s : ArmadaState) (t : Token) (b : Address) (x : Coins) : Prop :=
  match b with
  | .participant p =>
    ∃ e ∈ (s.book t).paymentsTo p, e ∈ s.pool.live t ∧ e.2 = ⟨cfg.payeeKey p, t, x⟩
  | .channel d =>
    ∃ e ∈ (s.chanOf t d).notes, e ∈ s.pool.live t ∧ e.2.value = x ∧ OwnedBy cfg.self e.2

/-! ### Chain level -/

/-- **Payout guarantee at note level** (Nitro `transfer_can_happen`,
    `directly_funded_pays`). On a finalized channel, an allocation entry that
    the channel affords a positive amount can be paid from the channel's
    notes, if a payout to a channel meets the minimum credit (`hcredit`). The
    payee gets a note of exactly the affordable amount. -/
theorem finalized_affordable_pays (hPool : PoolExecutes cfg) {s : ArmadaState}
    (hs : ArmadaReachable cfg apps s) {t : Token} {c : FixedPart} {b : Address}
    {o : Allocation} {amt : Coins}
    (hfin : (s.chanOf t c).status.finalOutcome s.now = some (.allocation o))
    (hb : o.find b = some ⟨b, .alloc amt⟩) (hpos : 0 < s.payout t c o b)
    (hcredit : CreditAllowed cfg s t b (s.payout t c o b)) :
    ∃ s', ArmadaStep cfg apps (.transfer t c b (s.chanOf t c).notes (s.payout t c o b)) s s' ∧
      PaidNote cfg s' t b (s.payout t c o b) := by
  sorry

/-- **Deposit at note level** (Nitro `deposit_can_happen`, restricted to the
    phases before finalization by ruling 3). If the depositor's pool step
    creates a deposit note of value `x` keyed to the adjudicator, a deposit
    with the current balance as `expectedHeld` executes, and the channel gets
    one new note of value `x`. -/
theorem deposit_can_happen_notes (hPool : PoolExecutes cfg) {s : ArmadaState}
    (hs : ArmadaReachable cfg apps s) {t : Token} {c : FixedPart} {x : Coins}
    {fund others : List Note} {d : Note} {ps1 : PoolState}
    (hOpen : (s.chanOf t c).status.IsOpen s.now)
    (hFund : ∀ e ∈ fund, ¬ OwnedBy cfg.self e.2)
    (hLeg1 : PoolCall s.pool ps1 t fund (d :: others))
    (hd : OwnedBy cfg.self d.2 ∧ d.2.value = x) :
    ∃ s', ArmadaStep cfg apps (.deposit t c (s.balance t c) x fund []) s s' ∧
      s'.balance t c = s.balance t c + x ∧ PaidNote cfg s' t c.address x := by
  sorry

/-- **Ledger top-up at note level** (Nitro `ledger_topup_deposit_funds`,
    Nitro:989-995). After a deposit of `a'` into the ledger `L` with
    `expectedHeld = a + b + c`, the ledger's notes total `a + b + c + a'`, one
    of them is the new merged note, and the reordered outcome affords `A`
    `a + a'` in full. -/
theorem ledger_topup_deposit_funds_notes {s s' : ArmadaState} (hs : ArmadaReachable cfg apps s)
    (t : Token) (L : FixedPart) (A B χ : Address) (a b c a' : Coins) (hAB : A ≠ B)
    (hAχ : A ≠ χ) (hBχ : B ≠ χ) (hheld : s.balance t L = a + b + c)
    {fund merged : List Note}
    (h : ArmadaStep cfg apps (.deposit t L (a + b + c) a' fund merged) s s') :
    s'.balance t L = a + b + c + a' ∧
    (∃ new keep, (s'.chanOf t L).notes = keep ++ [new] ∧ new ∈ s'.pool.live t ∧
      OwnedBy cfg.self new.2 ∧ new.2.value = notesValue merged + a') ∧
    Allocation.paidTo (s'.balance t L) [alloc B b, alloc χ c, alloc A (a + a')] A = a + a' ∧
    Allocation.paidTo (s'.balance t L) [alloc A (a + a'), alloc B b, alloc χ c] A = a + a' := by
  sorry

/-! ### Game level -/

/-- **Directly funded channel pays at note level** (Nitro
    `directly_funded_pays`, Nitro:779-781). On a finalized, directly funded
    channel `c`, `p` has a strategy with no wait to obtain payment notes worth
    its allocation entry, and to leave `c`'s entry for `p` fully paid. The
    second conjunct ties the payment to `c` (finding F2). `hentry` excludes a
    guarantee item at `p`'s address, which no transfer pays (Nitro
    `transfer_fails_otherwise`). -/
theorem directly_funded_pays_notes {p : Participant} (T : Threat p)
    (A : Assumptions cfg apps p T) (hPool : PoolExecutes cfg) (net : Net p)
    (hs : ArmadaReachable cfg apps net.chain) (t : Token) (c : FixedPart) (o : Allocation)
    (hf : (net.view t).Finalized c (.allocation o)) (hfund : (net.view t).chain.DirectlyFunded c)
    (hentry : o.owed p.address = 0 ∨ ∃ amt, o.find p.address = some ⟨p.address, .alloc amt⟩) :
    UnbeatableNoWait cfg apps T
      (fun net' => (net.chain.book t).paid p + o.owed p.address ≤ (net'.chain.book t).paid p ∧
        ∃ o', (net'.view t).Finalized c (.allocation o') ∧ o'.owed p.address = 0)
      net := by
  sorry

/-- **Ledger offload at note level** (Nitro `ledger_offload_funds_subchannel`,
    Nitro:859-865). A ledger channel funds its sub-channel `χ` for both
    participants: each can obtain a state in which `χ`'s notes total at least
    `c`. `hmin`: the credit `c` meets the minimum credit, because `χ` can
    finalize before `L` pays it. -/
theorem ledger_offload_funds_subchannel_notes (Ts : Threats cfg apps) (hPool : PoolExecutes cfg)
    (v : Views) (hv : v.Consistent) (hs : ∀ p, ArmadaReachable cfg apps (v p).chain)
    (t : Token) (w : Nitro.LedgerWithSub) (hw : HoldsLedgerWithSub cfg apps Ts v t w)
    (hmin : cfg.minCredit ≤ w.c) :
    FundedFor cfg apps (Ts.T w.A) t w.χ w.c (v w.A) ∧
    FundedFor cfg apps (Ts.T w.B) t w.χ w.c (v w.B) := by
  sorry

/-- **Partial withdrawal at note level** (Nitro `ledger_partial_withdrawal`,
    Nitro:997-1047). With the conclusion proof for
    `[L ↦ (L' : a + b + c, A : a')]` and `L`'s notes totalling
    `a + b + c + a'`, `A` obtains payment notes worth `a'` with no wait and
    leaves `L`'s entry for `A` fully paid (finding F2), and `L'`'s notes can
    be raised to `a + b + c` for `A` and for `B`. `hmin`: the credit into `L'`
    meets the minimum credit. -/
theorem ledger_partial_withdrawal_notes (Ts : Threats cfg apps) (hPool : PoolExecutes cfg)
    (v : Views) (hv : v.Consistent) (hs : ∀ p, ArmadaReachable cfg apps (v p).chain)
    (t : Token) (A B : Participant) (L L' χ : FixedPart) (a b c a' : Coins)
    (hL : IsLedgerChannel apps L) (hL' : IsLedgerChannel apps L') (hLp : L.participants = [A, B])
    (hL'p : L'.participants = [A, B]) (hLL' : L ≠ L') (hmin : cfg.minCredit ≤ a + b + c)
    (hbal : ∀ p, (v p).chain.balance t L = a + b + c + a')
    (hconc : Concluded (v.nitro t) L
      (.allocation [alloc L'.address (a + b + c), alloc A.address a']))
    (hsent : ∀ p, ∀ s ∈ (v p).sent, s.state.channel = L → s.state.isFinal = true →
      s.state.outcome = .allocation [alloc L'.address (a + b + c), alloc A.address a'])
    (hopen : ∀ p, ((v p).view t).chain.finalOutcome L.address = none)
    (hL'out : v.FinalizableBy cfg apps Ts t L'
      (.allocation [alloc A.address a, alloc B.address b, alloc χ.address c]) [A, B]) :
    UnbeatableNoWait cfg apps (Ts.T A)
      (fun net' => ((v A).chain.book t).paid A + a' ≤ (net'.chain.book t).paid A ∧
        ∃ o', (net'.view t).Finalized L (.allocation o') ∧ o'.owed A.address = 0) (v A) ∧
    FundedFor cfg apps (Ts.T A) t L' (a + b + c) (v A) ∧
    FundedFor cfg apps (Ts.T B) t L' (a + b + c) (v B) := by
  sorry

/-- **SATP Theorem 3.2 at note level** (Nitro `satp_theorem_3_2`,
    SATP:503-507). An honest intermediary `P` that completed Round 2 and holds
    the latest states of its two ledgers, whose notes cover the ledger
    outcomes, has a strategy to obtain payment notes worth its pre-protocol
    ledger balances `balm + balp`, with both ledgers finalized, no entry for
    `V` left, and `P`'s entries fully paid. The hypotheses are those of the
    Nitro theorem, read on the Nitro view of token `t`, plus the funding
    hypotheses `hfundm`, `hfundp`, the hypothesis `hnofinal` that `P` sent
    no final state of either ledger (finding F4), and `hminm`, `hminp`: the
    ledger outcomes obey the outcome rule, so `P` can challenge with them. -/
theorem satp_theorem_3_2_notes {P : Participant} (T : Threat P) (A : Assumptions cfg apps P T)
    (hPool : PoolExecutes cfg) (r : Route) (alice bob : Participant) (hr : r.WellFormed apps)
    (hV : apps r.V.appDef = satpVirtualRules)
    (halice : r.peers.head? = some alice) (hbob : r.peers.getLast? = some bob)
    (i : Nat) (hi : 1 ≤ i) (hin : i + 1 < r.peers.length) (hP : r.peers[i]? = some P)
    (Pprev Pnext : Participant) (hprev : r.peers[i - 1]? = some Pprev)
    (hnext : r.peers[i + 1]? = some Pnext)
    (Lm Lp : FixedPart) (hLm : r.ledgers[i - 1]? = some Lm) (hLp : r.ledgers[i]? = some Lp)
    (hdur : 0 < Lm.challengeDuration ∧ 0 < Lp.challengeDuration ∧ 0 < r.V.challengeDuration)
    (om op : Allocation) (balm balp : Coins)
    (hom : r.LedgerAfterRound2 om Pprev P balm r.b0)
    (hop : r.LedgerAfterRound2 op P Pnext balp r.a0)
    (net : Net P) (hs : ArmadaReachable cfg apps net.chain) (t : Token)
    (hHm : HoldsLatestLedger (net.view t) Lm om) (hHp : HoldsLatestLedger (net.view t) Lp op)
    (hVs : HoldsVirtualSetup (net.view t) r alice bob true)
    (hsetup : ∀ ss : Nitro.SignedState, ss.ByAll → ss.state.channel = r.V →
      ss.state.turnNum ≤ 1 → ss.state.outcome = originalOutcome alice bob r.a0 r.b0)
    (hchain : (net.view t).chain.finalOutcome Lm.address = none ∧
      (net.view t).chain.finalOutcome Lp.address = none ∧
      (net.view t).chain.finalOutcome r.V.address = none)
    (hfundm : om.total ≤ net.chain.balance t Lm) (hfundp : op.total ≤ net.chain.balance t Lp)
    (hnofinal : ∀ s ∈ net.sent, s.state.channel = Lm ∨ s.state.channel = Lp →
      s.state.isFinal = false)
    (hminm : OutcomeRespectsMin cfg om) (hminp : OutcomeRespectsMin cfg op) :
    Unbeatable cfg apps T
      (fun net' => (net.chain.book t).paid P + balm + balp ≤ (net'.chain.book t).paid P ∧
        ∃ om' op', (net'.view t).Finalized Lm (.allocation om') ∧
          (net'.view t).Finalized Lp (.allocation op') ∧
          om'.find r.V.address = none ∧ op'.find r.V.address = none ∧
          om'.owed P.address = 0 ∧ op'.owed P.address = 0) net := by
  sorry

/-- **SATP end-user theorem at note level** (Nitro `satp_end_user_recovers`,
    SATP:500-501). If `V` finalizes with `{A : a, B : b}`, Alice has a
    strategy to obtain payment notes worth her pre-protocol balance in `L₀`
    minus `a0` plus `a`, with `L₀` finalized, no entry for `V` left, and her
    entry fully paid, when `L₀`'s notes cover its outcome, she sent no final
    state of `L₀` (finding F4), and `L₀`'s outcome obeys the outcome rule. -/
theorem satp_end_user_recovers_notes {P : Participant} (T : Threat P)
    (A : Assumptions cfg apps P T) (hPool : PoolExecutes cfg) (r : Route) (alice bob : Participant)
    (hr : r.WellFormed apps) (hV : apps r.V.appDef = satpVirtualRules)
    (halice : r.peers.head? = some alice) (hbob : r.peers.getLast? = some bob)
    (hPA : P = alice) (P1 : Participant) (hP1 : r.peers[1]? = some P1)
    (L0 : FixedPart) (hL0 : r.ledgers[0]? = some L0)
    (hdur : 0 < L0.challengeDuration ∧ 0 < r.V.challengeDuration)
    (o : Allocation) (bal : Coins) (ho : r.LedgerAfterRound2 o P P1 bal r.a0)
    (net : Net P) (hs : ArmadaReachable cfg apps net.chain) (t : Token)
    (hH : HoldsLatestLedger (net.view t) L0 o)
    (hVs : HoldsVirtualSetup (net.view t) r alice bob true)
    (a b : Coins)
    (hfin : (net.view t).Finalized r.V (.allocation [alloc alice.address a, alloc bob.address b]))
    (hchain : (net.view t).chain.finalOutcome L0.address = none)
    (hfund : o.total ≤ net.chain.balance t L0)
    (hnofinal : ∀ s ∈ net.sent, s.state.channel = L0 → s.state.isFinal = false)
    (hmin : OutcomeRespectsMin cfg o) :
    Unbeatable cfg apps T
      (fun net' => (net.chain.book t).paid P + bal + a ≤ (net'.chain.book t).paid P + r.a0 ∧
        ∃ o', (net'.view t).Finalized L0 (.allocation o') ∧ o'.find r.V.address = none ∧
          o'.owed P.address = 0) net := by
  sorry

end ArmadaLean.ArmadaNitro
