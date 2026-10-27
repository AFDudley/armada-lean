/-
  Armada adjudicator: safety theorems. Attribution, conservation, phase
  rules and non-interference. See `docs/armada-nitro-theorems.md` for the
  table of meanings, sources and rulings.

  Shapes reused from prior work (armada-laconic
  `labbook/2026-10-26-utxo-channel-formalizations.md`, section (c)):
  * Attribution and conservation follow Hydra's `solvency`
    (`Solvency.lagda.typ`:395-397): one invariant over every reachable state
    that ties each channel's value to its own outputs.
  * Spend authority follows LeanDY's `spent_by_base_transaction`
    (`Soundness.lean`:670-684): if a channel note is spent, the spend is a
    protocol-shaped call on that channel (`spend_of_channel_note`,
    `finalized_spend_permitted`).

  Every theorem has proof `sorry`; the statements are the deliverable.
-/
import ArmadaLean.ArmadaNitro.Refinement

namespace ArmadaLean.ArmadaNitro

set_option autoImplicit false

open ArmadaLean.Nitro (Coins Participant FixedPart Address Allocation Mode Apps)

variable {cfg : Config} {apps : Apps}

/-! ### The pool -/

/-- The pool state of a reachable Armada state is a reachable pool state. So
    every pool theorem over `Reachable` (`core_invariant`,
    `live_note_unspent`, `spend_not_blocked`, ...) applies to it. -/
theorem pool_reachable {s : ArmadaState} (hs : ArmadaReachable cfg apps s) :
    _root_.Reachable s.pool := by
  sorry

/-! ### Attribution (ruling 2; utxo labbook issue I4) -/

/-- A channel's Nitro balance is the total value of its own notes. -/
theorem balance_eq_notes_total {s : ArmadaState} (hs : ArmadaReachable cfg apps s) (t : Token)
    (c : FixedPart) :
    (toNitro s t).balances.get c.address = notesValue (s.chanOf t c).notes := by
  sorry

/-- A participant's Nitro balance is the total value of the notes the
    adjudicator paid to it. -/
theorem paid_eq_payment_notes {s : ArmadaState} (hs : ArmadaReachable cfg apps s) (t : Token)
    (p : Participant) :
    (toNitro s t).balances.get (.participant p) = notesValue ((s.book t).paymentsTo p) := by
  sorry

/-- Every channel note is a live pool note of the channel's token, keyed to
    the adjudicator. -/
theorem channel_notes_live_owned {s : ArmadaState} (hs : ArmadaReachable cfg apps s)
    {t : Token} {c : FixedPart} {e : Note} (he : e ∈ (s.chanOf t c).notes) :
    e ∈ s.pool.live t ∧ OwnedBy cfg.self e.2 := by
  sorry

/-- A channel holds each note once. -/
theorem channel_notes_nodup {s : ArmadaState} (hs : ArmadaReachable cfg apps s) (t : Token)
    (c : FixedPart) : (s.chanOf t c).notes.Nodup := by
  sorry

/-- A note belongs to at most one channel. -/
theorem channel_notes_disjoint {s : ArmadaState} (hs : ArmadaReachable cfg apps s)
    {t : Token} {c c' : FixedPart} {e : Note} (he : e ∈ (s.chanOf t c).notes)
    (he' : e ∈ (s.chanOf t c').notes) : c = c' := by
  sorry

/-- Every payment note of `p` has `p`'s payee key and the token of its
    record (ruling 4). -/
theorem payment_notes_keyed {s : ArmadaState} (hs : ArmadaReachable cfg apps s)
    {t : Token} {p : Participant} {e : Note} (he : e ∈ (s.book t).paymentsTo p) :
    e.2.npk = cfg.payeeKey p ∧ e.2.token = t := by
  sorry

/-- A transfer on channel `c` spends exactly its listed notes, and they are
    `c`'s notes. -/
theorem transfer_spends_own_notes {s s' : ArmadaState} {t : Token} {c : FixedPart} {b : Address}
    {ins : List Note} (h : ArmadaStep cfg apps (.transfer t c b ins) s s') :
    (∀ e, Spends s.pool s'.pool t e ↔ e ∈ ins) ∧ ∀ e ∈ ins, e ∈ (s.chanOf t c).notes := by
  sorry

/-- A deposit into channel `c` spends exactly the depositor's notes `fund` and
    the channel notes `merged`. The `merged` notes are `c`'s notes. No `fund`
    note is keyed to the adjudicator. -/
theorem deposit_spends_own_notes {s s' : ArmadaState} {t : Token} {c : FixedPart}
    {expectedHeld x : Coins} {fund merged : List Note}
    (h : ArmadaStep cfg apps (.deposit t c expectedHeld x fund merged) s s') :
    (∀ e, Spends s.pool s'.pool t e ↔ e ∈ fund ∨ e ∈ merged) ∧
    (∀ e ∈ merged, e ∈ (s.chanOf t c).notes) ∧ ∀ e ∈ fund, ¬ OwnedBy cfg.self e.2 := by
  sorry

/-- Reclaim, challenge, checkpoint, conclude and tick do not change the
    pool. -/
theorem status_call_keeps_pool {call : Call} {s s' : ArmadaState}
    (h : ArmadaStep cfg apps call s s')
    (hcall : (∃ t l v, call = .reclaim t l v) ∨
      (∃ t p c proof candidate, call = .challenge t p c proof candidate) ∨
      (∃ t c proof candidate, call = .checkpoint t c proof candidate) ∨
      (∃ t c ss, call = .conclude t c ss) ∨ (∃ dt, call = .tick dt)) :
    s'.pool = s.pool := by
  sorry

/-- **Spend authority (LeanDY shape).** A step that spends a note of channel
    `c` is a deposit into `c` that merges it, or a transfer on `c` that pays
    from it. A call on channel `c` spends only `c`'s notes. -/
theorem spend_of_channel_note {s s' : ArmadaState} (hs : ArmadaReachable cfg apps s)
    {call : Call} (h : ArmadaStep cfg apps call s s') {t : Token} {c : FixedPart} {e : Note}
    (he : e ∈ (s.chanOf t c).notes) (hsp : Spends s.pool s'.pool t e) :
    (∃ expectedHeld x fund merged, call = .deposit t c expectedHeld x fund merged ∧ e ∈ merged) ∨
    (∃ b ins, call = .transfer t c b ins ∧ e ∈ ins) := by
  sorry

/-! ### Conservation (Hydra solvency shape) -/

/-- **Conservation.** For each token, the sum of the channel balances equals
    the value of the adjudicator's notes in the pool: the live notes that the
    adjudicator attributes to a channel. -/
theorem held_eq_live_adjudicator_value {s : ArmadaState} (hs : ArmadaReachable cfg apps s)
    (t : Token) :
    (toNitro s t).held =
      notesValue ((s.pool.live t).filter (fun e => decide (e ∈ s.attributed t))) := by
  sorry

open Classical in
/-- The sum of the channel balances is at most the value of all live notes
    keyed to the adjudicator. The difference is the notes that other pool
    users sent to the adjudicator's key outside a deposit. No channel counts
    them (open design choice D3). -/
theorem channel_total_le_owned_value {s : ArmadaState} (hs : ArmadaReachable cfg apps s)
    (t : Token) :
    (toNitro s t).held ≤
      notesValue ((s.pool.live t).filter (fun e => decide (OwnedBy cfg.self e.2))) := by
  sorry

/-- The adjudicator holds no more of a token than the pool's custody of it
    (`core_invariant`, PoolSafety.lean:166). -/
theorem adjudicator_held_le_pool_held {s : ArmadaState} (hs : ArmadaReachable cfg apps s)
    (t : Token) : (toNitro s t).held ≤ s.pool.held t := by
  sorry

/-- A transfer moves no token out of the pool: the payee receives a note
    (ruling 4), so the pool's custody and its unshield record do not change. -/
theorem transfer_keeps_custody {s s' : ArmadaState} {t : Token} {c : FixedPart} {b : Address}
    {ins : List Note} (h : ArmadaStep cfg apps (.transfer t c b ins) s s') :
    s'.pool.held = s.pool.held ∧ s'.pool.payouts = s.pool.payouts := by
  sorry

/-! ### Phase rules (ruling 3; utxo labbook issue I2) -/

/-- A deposit happens only before finalization. -/
theorem deposit_requires_not_finalized {s s' : ArmadaState} {t : Token} {c : FixedPart}
    {expectedHeld x : Coins} {fund merged : List Note}
    (h : ArmadaStep cfg apps (.deposit t c expectedHeld x fund merged) s s') :
    (s.chanOf t c).status.mode s.now ≠ .finalized := by
  sorry

/-- A deposit happens only when the channel's balance is `expectedHeld`
    (ruling 5; go-nitro MultiAssetHolder.sol:51). -/
theorem deposit_requires_expectedHeld {s s' : ArmadaState} {t : Token} {c : FixedPart}
    {expectedHeld x : Coins} {fund merged : List Note}
    (h : ArmadaStep cfg apps (.deposit t c expectedHeld x fund merged) s s') :
    s.balance t c = expectedHeld := by
  sorry

/-- A transfer happens only after finalization. -/
theorem transfer_requires_finalized {s s' : ArmadaState} {t : Token} {c : FixedPart}
    {b : Address} {ins : List Note} (h : ArmadaStep cfg apps (.transfer t c b ins) s s') :
    (s.chanOf t c).status.mode s.now = .finalized := by
  sorry

/-- A reclaim happens only after both channels are finalized. -/
theorem reclaim_requires_finalized {s s' : ArmadaState} {t : Token} {l v : FixedPart}
    (h : ArmadaStep cfg apps (.reclaim t l v) s s') :
    (s.chanOf t l).status.mode s.now = .finalized ∧
    (s.chanOf t v).status.mode s.now = .finalized := by
  sorry

/-- **Merges only before finalization.** A step that spends a note of a
    channel that is not finalized is a deposit into that channel. -/
theorem open_channel_spend_is_deposit {s s' : ArmadaState} (hs : ArmadaReachable cfg apps s)
    {call : Call} (h : ArmadaStep cfg apps call s s') {t : Token} {c : FixedPart} {e : Note}
    (he : e ∈ (s.chanOf t c).notes) (hsp : Spends s.pool s'.pool t e)
    (hopen : (s.chanOf t c).status.mode s.now ≠ .finalized) :
    ∃ expectedHeld x fund merged, call = .deposit t c expectedHeld x fund merged ∧ e ∈ merged := by
  sorry

/-- **Spends only after finalization are transfers.** A step that spends a note
    of a finalized channel is a transfer on that channel. -/
theorem finalized_channel_spend_is_transfer {s s' : ArmadaState}
    (hs : ArmadaReachable cfg apps s) {call : Call} (h : ArmadaStep cfg apps call s s')
    {t : Token} {c : FixedPart} {e : Note} (he : e ∈ (s.chanOf t c).notes)
    (hsp : Spends s.pool s'.pool t e) (hfin : (s.chanOf t c).status.mode s.now = .finalized) :
    ∃ b ins, call = .transfer t c b ins ∧ e ∈ ins := by
  sorry

/-- A finalized channel stays finalized (Nitro `finalized_permanent`). -/
theorem finalized_channel_stays_finalized {call : Call} {s s' : ArmadaState}
    (h : ArmadaStep cfg apps call s s') {t : Token} {c : FixedPart}
    (hfin : (s.chanOf t c).status.mode s.now = .finalized) :
    (s'.chanOf t c).status.mode s'.now = .finalized := by
  sorry

/-! ### Non-interference (utxo labbook issue I3) -/

/-- **Only permitted payouts spend a finalized channel's notes.** Once channel
    `c` is finalized with allocation `o`, a step that spends a note of `c` is
    a transfer on `c` of an allocation entry of `o` that `c` affords, and it
    creates the payout note of exactly the affordable amount with the payee's
    note key. -/
theorem finalized_spend_permitted {s s' : ArmadaState} (hs : ArmadaReachable cfg apps s)
    {t : Token} {c : FixedPart} {o : Allocation}
    (hfin : (s.chanOf t c).status.finalOutcome s.now = some (.allocation o))
    {call : Call} (h : ArmadaStep cfg apps call s s') {e : Note}
    (he : e ∈ (s.chanOf t c).notes) (hsp : Spends s.pool s'.pool t e) :
    ∃ b ins amt, call = .transfer t c b ins ∧ e ∈ ins ∧ o.find b = some ⟨b, .alloc amt⟩ ∧
      0 < s.payout t c o b ∧
      ∃ pay, Creates s.pool s'.pool t pay ∧ pay.2.value = s.payout t c o b ∧
        PayKey cfg b pay.2 := by
  sorry

/-- **The pool checks of a channel spend stay true** across every step that is
    not a deposit into or a transfer on that channel. The pool's
    `spend_not_blocked` (PoolSafety.lean:1797) gives this for one pool step;
    attribution gives it for the adjudicator's own pool steps on other
    channels. -/
theorem channel_spend_not_blocked {s s' : ArmadaState} (hs : ArmadaReachable cfg apps s)
    {call : Call} (h : ArmadaStep cfg apps call s s') {t : Token} {c : FixedPart}
    {tn : Nat} {root nk : Term} {entries : List Note}
    (hOwn : ∀ e ∈ entries, e ∈ (s.chanOf t c).notes) (hTree : ∀ e ∈ entries, e.1.1 = tn)
    (hEnabled : SpendEnabled s.pool tn root t entries (entries.map fun e => nullifier nk e.1.2))
    (hNotDeposit : ¬ ∃ expectedHeld x fund merged, call = .deposit t c expectedHeld x fund merged)
    (hNotTransfer : ¬ ∃ b ins, call = .transfer t c b ins) :
    SpendEnabled s'.pool tn root t entries (entries.map fun e => nullifier nk e.1.2) := by
  sorry

/-- **Non-interference for a pending payout.** Let channel `c` be finalized
    with allocation `o`, and let the transfer of `c`'s entry for `b` from the
    notes `ins` be executable at `s`. After any step by any caller, the same
    transfer is still executable, or the step is one of:
    * a transfer on `c` (it pays one of `c`'s outcome entries);
    * a reclaim with ledger `c` (it redistributes one of `c`'s outcome
      entries, a guarantee);
    * a transfer on another channel that credits `c`, while `c` does not
      afford `b`'s entry in full. The credit raises the affordable amount, and
      a pending payout fixes its amount in its pool proof.
    The third case is the counterexample to the strong reading "only by paying
    one of `c`'s outcome entries" (`docs/armada-nitro-theorems.md`, finding
    F1). -/
theorem pending_payout_not_blocked {s s' : ArmadaState} (hs : ArmadaReachable cfg apps s)
    {t : Token} {c : FixedPart} {b : Address} {ins : List Note} {o : Allocation}
    (hfin : (s.chanOf t c).status.finalOutcome s.now = some (.allocation o))
    (hEn : CallEnabled cfg apps s (.transfer t c b ins))
    {call : Call} (h : ArmadaStep cfg apps call s s') :
    CallEnabled cfg apps s' (.transfer t c b ins) ∨
    (∃ b' ins', call = .transfer t c b' ins') ∨
    (∃ v, call = .reclaim t c v) ∨
    (∃ d ins', call = .transfer t d c.address ins' ∧
      ¬ o.Affords (s.balance t c) b (o.owed b)) := by
  sorry

end ArmadaLean.ArmadaNitro
