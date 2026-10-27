# The Armada adjudicator: Nitro over Armada pool notes

This file records the Armada adjudicator specification under `ArmadaLean/ArmadaNitro/`. The Armada adjudicator is Nitro, as `ArmadaLean/Nitro/` specifies it (`docs/nitro-theorems.md`), whose escrowed assets are notes in the Armada pool (`ArmadaLean/Pool.lean`, `docs/pool-symbolic-changes.md`). The deliverable is the definitions and the theorem types. Every theorem has proof `sorry`, so the sorry count equals the theorem count (40).

Inputs: the operator rulings of 2026-10-27 (below); armada-laconic `labbook/2026-10-26-utxo-channel-formalizations.md` (Hydra solvency shape, LeanDY spend-authority shape); armada-laconic `labbook/2026-10-26-adjudicator-layout-audit.md` (what the old model on `adjudicator-model-v4` did wrong); `docs/lean/writing-lean.md` (rules 1, 2, 9, 10, 11).

## Modules

| Module | Content |
|---|---|
| `Notes.lean` | `Note`, `notesValue`, `Config` (adjudicator address, payee keys), `OwnedBy`, `Creates`, `PoolCall` (one pool `Step` with an exact note effect), `OtherUserStep` (the environment), `OwnedSpendable`, `PoolExecutes` (the pool interface of the liveness theorems) |
| `State.lean` | `Channel` (status and notes), `Holder` (one token's record), `ArmadaState`, the abstraction `toNitro`, `genesis`, `NitroEquiv` |
| `Operations.lean` | `Call`, `Call.toNitro`, `PayKey`, `ArmadaStep`, `ArmadaReachable`, `CallEnabled` |
| `Refinement.lean` | 7 theorems: the refinement of Nitro and the carry-over principles |
| `Safety.lean` | 25 theorems: attribution, conservation, phase rules, non-interference |
| `Strategy.lean` | the Nitro §4 game over the Armada system (relational moves) |
| `Liveness.lean` | 8 theorems: note-level payout, deposit, ledger top-up, offload, partial withdrawal, SATP Theorem 3.2, end-user theorem |

## How the operator rulings are implemented

1. **No contract layout or encoding.** No storage slot, stored hash, sentinel, fixed width, allow-list or batch call. A channel status stores its outcome (`Nitro.ChannelStatus`). The adjudicator address is a term (`Config.self`), not a derivation from creation inputs (audit A2). No circuit width appears in `ArmadaNitro/`: the pool's shapes stay behind `PoolExecutes`. A batch is a sequence of calls (audit A9).
2. **The adjudicator is an ordinary pool user.** Every note operation is a pool `Step` (`PoolCall.step`), described by its effect on `PoolState.live` (`Spends`, `Creates`). The adjudicator never restates the pool's state update (writing-lean rule 1; audit A10). Its notes have note keys `npk self r` (`OwnedBy`). A channel's balance is the total value of its notes (`Channel.balance`); `toNitro` maps it to the Nitro balance of the channel.
3. **Channels with phases and own notes.** `Channel := {status, notes}`. The phases are Nitro `Mode` through `ChannelStatus.mode`. A deposit merges the channel notes `merged` with the deposit note into one note, only while the channel is not finalized (`ArmadaStep.deposit`, `hOpen`). A transfer needs a finalized channel, spends only the channel's notes `ins`, and returns one change note to the channel (`ArmadaStep.transfer`). A reclaim needs finalized channels and spends no note. There is no merge call.
4. **Payout keys.** A participant destination is paid a note keyed to `Config.payeeKey p`, a user note key (`Config.payeeKey_user`). A channel destination is credited with a new note keyed to the adjudicator and attributed to that channel (`PayKey`, `ArmadaState.credit`).
5. **`expectedHeld`.** `Call.deposit` carries `expectedHeld`; the step requires `s.balance t c = expectedHeld` (`hHeld`). The model has no forks and no finality: `ArmadaReachable` is every history from a deployment.
6. **Multi-asset, `Bool` rules, structured app data.** `ArmadaState.book : Token → Holder` is one independent copy per token; the pool and the clock are shared. App rules and app data are the Nitro ones (`Rules.supports : … → Bool`, `AppData`).

## Theorems (40)

Column "Ruling" names the operator ruling of 2026-10-27 that the theorem implements or depends on.

### Refinement (`Refinement.lean`)

| Theorem | Meaning | Refines / uses | Ruling |
|---|---|---|---|
| `toNitro_genesis` | A deployment is the Nitro genesis, up to `NitroEquiv`. | Nitro `Adjudicator.genesis` | 2 |
| `nitroEquiv_apply` | No Nitro operation tells two `NitroEquiv` adjudicators apart. | Nitro `Adjudicator.apply` | 1 |
| `step_refines` | Every Armada step is the Nitro operation `call.toNitro t` on the abstraction, or no observable change for token `t`. | Nitro `Adjudicator.apply`, `Step` | 2, 3, 6 |
| `toNitro_reachable` | The abstraction of a reachable Armada state is a reachable Nitro state, up to `NitroEquiv`. | Nitro `Reachable`; uses `step_refines`, `nitroEquiv_apply` | 2, 5 |
| `nitro_invariant_carries` | An `NitroEquiv`-invariant property of every reachable Nitro state holds on every reachable Armada abstraction. | Nitro `Reachable` | 2 |
| `nitro_step_carries` | An `NitroEquiv`-invariant step relation of Nitro holds across every Armada step, or the step is not observable. | Nitro `Step` | 2 |
| `nitro_status_call_lifts` | A Nitro reclaim, challenge, checkpoint, conclude or tick on the abstraction is an Armada step that keeps the pool. | Nitro `reclaim_can_happen`, `challenge_can_happen`, `checkpoint_can_happen`, `conclude_can_happen` | 3, 6 |

### Attribution (`Safety.lean`)

| Theorem | Meaning | Refines / uses | Ruling |
|---|---|---|---|
| `pool_reachable` | The pool state of a reachable Armada state is reachable, so every pool theorem applies. | pool `Reachable` | 2 |
| `balance_eq_notes_total` | A channel's Nitro balance is the total value of its own notes. | Nitro `Balances.get` | 2 |
| `paid_eq_payment_notes` | A participant's Nitro balance is the total value of its payment notes. | Nitro `Balances.get`, `payTo` | 4 |
| `channel_notes_live_owned` | Every channel note is live in the pool and keyed to the adjudicator. | pool `live`; Hydra `solvency` | 2 |
| `channel_notes_nodup` | A channel holds each note once. | pool `LiveSpentInvariant` | 2 |
| `channel_notes_disjoint` | A note belongs to at most one channel. | utxo labbook I4 | 2, 3 |
| `payment_notes_keyed` | A payment note of `p` has `p`'s payee key and the record's token. | — | 4 |
| `transfer_spends_own_notes` | A transfer on `c` spends exactly its listed notes, which are `c`'s notes. | pool `Spends` | 3 |
| `deposit_spends_own_notes` | A deposit into `c` spends exactly the depositor's `fund` and `c`'s `merged` notes. | pool `Spends` | 3 |
| `status_call_keeps_pool` | Reclaim, challenge, checkpoint, conclude and tick do not change the pool. | Nitro `reclaim_effects` (no coins move) | 3 |
| `spend_of_channel_note` | A step that spends a note of `c` is a deposit into `c` or a transfer on `c` (LeanDY shape). | LeanDY `spent_by_base_transaction`; pool `owned_owner_binding` through `OtherUserStep` | 2, 3 |

### Conservation (`Safety.lean`)

| Theorem | Meaning | Refines / uses | Ruling |
|---|---|---|---|
| `held_eq_live_adjudicator_value` | Per token, the sum of the channel balances equals the value of the adjudicator's attributed live notes. | Hydra `solvency`; Nitro `held_eq_channel_balances` | 2, 6 |
| `channel_total_le_owned_value` | Per token, the sum of the channel balances is at most the value of all live notes keyed to the adjudicator. | — (design choice D3) | 2 |
| `adjudicator_held_le_pool_held` | The adjudicator holds no more of a token than the pool's custody. | pool `core_invariant` | 2 |
| `transfer_keeps_custody` | A transfer changes neither the pool's custody nor its unshield record. | pool `Step.transactOwned` (no unshield) | 4 |

### Phase rules (`Safety.lean`)

| Theorem | Meaning | Refines / uses | Ruling |
|---|---|---|---|
| `deposit_requires_not_finalized` | A deposit happens only before finalization. | Hydra `s-inc`; not in Nitro (Nitro allows a deposit at any time) | 3 |
| `deposit_requires_expectedHeld` | A deposit happens only when the balance is `expectedHeld`. | Nitro `deposit_requires_expectedHeld` | 5 |
| `transfer_requires_finalized` | A transfer happens only after finalization. | Nitro `transfer_requires_finalized` | 3 |
| `reclaim_requires_finalized` | A reclaim happens only after both channels are finalized. | Nitro `reclaim_requires` | 3 |
| `open_channel_spend_is_deposit` | A step that spends a note of a non-finalized channel is a deposit into it (merges only before finalization). | utxo labbook I2 | 3 |
| `finalized_channel_spend_is_transfer` | A step that spends a note of a finalized channel is a transfer on it. | utxo labbook I2 | 3 |
| `finalized_channel_stays_finalized` | A finalized channel stays finalized. | Nitro `finalized_permanent` | 3 |

### Non-interference (`Safety.lean`)

| Theorem | Meaning | Refines / uses | Ruling |
|---|---|---|---|
| `finalized_spend_permitted` | After finalization, a step that spends a note of `c` is a transfer of an allocation entry of `c`'s outcome, of the positive affordable amount, which creates the payout note with the payee's key. | LeanDY `spent_by_base_transaction`; Nitro `transfer_effects` | 3, 4 |
| `channel_spend_not_blocked` | The pool checks of a spend of `c`'s notes stay true across every step that is not a deposit into or a transfer on `c`. | pool `spend_not_blocked` | 2, 3 |
| `pending_payout_not_blocked` | A pending transfer on finalized `c` stays executable, unless the step is a transfer on `c`, a reclaim with ledger `c`, or a credit to `c` while `c` does not afford the entry in full (finding F1). | pool `spend_not_blocked`; Nitro `Allocation.paidTo` | 3, 4, 5 |

### Liveness (`Liveness.lean`)

| Theorem | Meaning | Refines / uses | Ruling |
|---|---|---|---|
| `finalized_affordable_pays` | On a finalized channel, an entry that the channel affords a positive amount can be paid from its notes; the payee gets a note of that amount. | Nitro `transfer_can_happen`; `PoolExecutes` | 3, 4 |
| `deposit_can_happen_notes` | Before finalization, a deposit with the current balance as `expectedHeld` executes and adds one note of the deposit's value. | Nitro `deposit_can_happen` (restricted to non-finalized channels) | 3, 5 |
| `ledger_topup_deposit_funds_notes` | After a top-up deposit, the ledger's notes total `a + b + c + a'`, the merged note is live, and the reordered outcome affords `A` `a + a'`. | Nitro `ledger_topup_deposit_funds` | 3, 5 |
| `directly_funded_pays_notes` | A directly funded finalized channel pays `p` its entry as notes, with no wait, and leaves the entry fully paid. | Nitro `directly_funded_pays`; `pending_payout_not_blocked` | 3, 4 |
| `ledger_offload_funds_subchannel_notes` | A ledger channel funds its sub-channel: both participants can raise the sub-channel's notes to `c`. | Nitro `ledger_offload_funds_subchannel` | 2, 4 |
| `ledger_partial_withdrawal_notes` | A partial withdrawal pays `A` `a'` as notes with no wait and funds the new ledger for `A` and `B`. | Nitro `ledger_partial_withdrawal` | 2, 4 |
| `satp_theorem_3_2_notes` | An honest intermediary obtains payment notes worth its pre-protocol ledger balances, with both ledgers finalized and no entry for `V` left. | Nitro `satp_theorem_3_2` (SATP Theorem 3.2) | 2, 4 |
| `satp_end_user_recovers_notes` | Alice obtains payment notes worth her pre-protocol balance minus `a0` plus `a`. | Nitro `satp_end_user_recovers` | 2, 4 |

## Nitro theorems through the refinement

`step_refines` is one-way: every Armada step is a Nitro step, not the reverse. The following list classifies the 93 theorems of `docs/nitro-theorems.md`.

- **Carry over unchanged, because they read no adjudicator state.** `channel_address_inj`, `channel_address_ne_participant`, `balances_absent_zero`, `balances_total_split`, `payout_priority_formula`, `payout_earlier_paid_in_full`, `payout_bounded`, `paidTo_first_entry_only`, `affords_when_fully_funded`, `reduceOwed_owed`, `forceMove_supports_valid_run`, `forceMove_conclude_keeps_outcome`, `mover_determined_by_turn`, `mover_cyclic`, `isOpen_iff`, `ledger_topup_reorder_safe`, `satp_outcome_change_keeps_total`, `turbo_value_exists_unique`.
- **Carry over by `nitro_invariant_carries`** (statement over `Nitro.Reachable`, invariant under `NitroEquiv`): `finalized_two_ways`, `satp_lemma_3_1`, `deposit_respects_funding_order` (with `step_refines` for its one step). `held_eq_channel_balances` holds on every abstraction by the definition of `toNitro`; `held_eq_live_adjudicator_value` is its note-level form.
- **Carry over by `nitro_step_carries`** (statement over one `Nitro.Step`): `paid_out_monotone`, `finalized_permanent`, `finalized_outcome_only_redistributed`, `turnNumRecord_monotone`.
- **Carry over by `step_refines`** (statement about one `apply` result; a "fails" theorem carries by the contrapositive): `deposit_effects`, `deposit_requires_expectedHeld`, `deposit_to_participant_fails` (an Armada deposit takes a channel by its type), `held_falls_only_by_payout`, `channel_balance_falls_only_by_redistribution`, `transfer_effects`, `transfer_fails_otherwise`, `transfer_zero_moves_nothing`, `transfer_requires_finalized`, `redistribution_ignores_caller`, `redistribution_conserves_total`, `challenge_requires`, `challenge_fails_when_finalized`, `rechallenge_equal_turn_fails`, `challenge_effects`, `checkpoint_requires`, `conclude_requires`, `conclude_needs_all`, `conclude_moves_no_value`, `reclaim_requires`, `reclaim_effects`, `reclaim_fails_without_entries`, `held_changes_only_by_deposit_payout`, `tick_moves_only_time`, `timeout_finalizes`, `challenge_in_progress_before_deadline`, `mode_of_absent`, `funding_decoupled_from_rules`, `failed_op_no_effect`.
- **Can-happen theorems.** They do not carry over by the refinement. `challenge_can_happen`, `checkpoint_can_happen`, `conclude_can_happen` and `reclaim_can_happen` lift by `nitro_status_call_lifts`. `transfer_can_happen` has the note-level form `finalized_affordable_pays`. `deposit_can_happen` holds in Armada only before finalization (`deposit_can_happen_notes`); after finalization it is false by ruling 3. `deposits_in_order_succeed` is not restated.
- **Restated at note level** (`Liveness.lean`): `directly_funded_pays` (as `directly_funded_pays_notes`), `ledger_offload_funds_subchannel`, `ledger_partial_withdrawal`, `satp_theorem_3_2`, `satp_end_user_recovers` (game level, each with the suffix `_notes`), and `ledger_topup_deposit_funds` (chain level, as `ledger_topup_deposit_funds_notes`).
- **Game theorems, not restated.** The Nitro game runs over the Nitro chain, so its theorems do not carry over. `Strategy.lean` states the same game over the Armada system. Not restated: `finalizable_funded_pays`, `conclusion_proof_finalizable`, `latest_state_finalizable`, `late_observer_can_checkpoint`, `finalizable_unique`, `channel_finalizability_cases`, `finalizable_or_two_enabled`, `single_enabled_is_finalizable`, `finalizable_is_enabled`, `funding_point_universally_finalizable`, `concluded_universally_finalizable`, `consensus_enabled_outcomes`, `turbo_redistribution_unbeatable`, `deposit_bounds_value`, `payout_to_other_affects_only_owner`, `participant_can_prevent_cycles`, `turbo_value_upper_bound`, `turbo_value_achievable`, `turbo_value_is_value`, `turbo_order_independent`, `subchannel_open_value_preserving`, `subchannel_close_value_preserving`, `satp_peers_can_finalize`, `satp_intermediary_before_round2`, `satp_reclaim_credits_intermediary` (its chain part carries by `step_refines` and `status_call_keeps_pool`).

## Findings

- **F1. The strong non-interference reading is false.** Ruling text: "another caller can make a pending payout on C stale only by paying one of C's outcome entries". Counterexample: `c` is finalized with outcome `[p : 10]` and one note of value 4. The pending payout is `transfer t c p.address [n4] 4`. Channel `d` is finalized with outcome `[c : 3]` and holds 3. Another caller runs the transfer of `d`'s entry for `c`. Then `c`'s balance is 7 and the affordable amount is 7, so the pending payout of 4 fails the amount check. The step pays one of `d`'s entries, not one of `c`'s. The cause: the pool proof fixes the payout amount, and go-nitro's transfer pays the whole affordable amount. `pending_payout_not_blocked` states the true form: a credit can make a payout stale only while `c` does not afford the entry in full. A reclaim with ledger `c` can also change the affordable amount; the theorem lists it with the payouts on `c`. The note-level reading of the ruling holds as stated: `finalized_spend_permitted`.
- **F2. A Nitro "balance rises" goal does not say which channel pays.** `directly_funded_pays` and `ledger_partial_withdrawal` have the goal "`p`'s participant balance rises by `x`". `p` can reach it with its own coins: deposit into a fresh channel whose only participant is `p`, conclude it, and transfer to itself. [INFERENCE: argument by hand, not checked in Lean.] The note-level forms add the conjunct that the named channel's entry for `p` is fully paid.
- **F3. A zero-amount transfer must spend no note.** If a transfer that affords nothing spent the channel's notes and returned them as change, any caller could repeat it at no cost and make every pending payout on the channel stale. The payout guarantee in the game would then be false. `ArmadaStep.transferZero` spends no note.
- **F4. The Nitro SATP intermediary theorems lack a hypothesis.** `satp_theorem_3_2` and `satp_end_user_recovers` allow that `P` sent an earlier final state of a ledger. The other peer can sign it and conclude the ledger at once with that older outcome, before `P` moves. [INFERENCE: argument by hand, not checked in Lean.] The note-level forms take `hnofinal`: `P` sent no final state of the ledgers. The approved Nitro texts are unchanged; the operator decides whether they change.
- **F5. Multi-input owned spends need owned verifying keys with more than one input.** The deployed owned circuits have one input (`docs/pool-symbolic-changes.md`, theorem 3). A deposit merge and a transfer from several notes need `N > 1`. `PoolExecutes` assumes them.

## Design choices the rulings do not settle

- **D1. The pool interface.** `PoolExecutes` assumes that the pool executes every owned spend of live adjudicator notes. The deployed pool has at most 8 inputs in one tree, at most 4 outputs, and a 120-bit range check (`Spendable`). A channel with many small notes, or notes in two trees, cannot be spent in one call. Options: limit the number of notes per channel, or let one call make several pool steps.
- **D2. Payee keys.** `Config.payeeKey : Participant → Term` gives each participant one fixed note key for all payouts. That key links all payouts to one participant. A per-channel or per-state key, carried in the fixed part or the outcome, is an alternative.
- **D3. Notes sent to the adjudicator outside a deposit.** Any pool user can create a note keyed to `npk self r`. No channel counts it, and the adjudicator never spends it, so its value is locked. `channel_total_le_owned_value` is therefore an inequality.
- **D4. Zero-value change notes.** A transfer always returns one change note, of value 0 when the inputs equal the payout.
- **D5. Consolidation inside a transfer.** A transfer may spend several channel notes and returns one change note, so it consolidates them. The ruling allows merges only inside a deposit; this model reads a transfer's change as part of the transfer.
- **D6. The deposit's first leg.** A deposit is two pool steps in one call: the depositor's step (any pool step that spends no adjudicator note and creates the deposit note, for example a shield or a transact) and the adjudicator's merge. The adapt binding of the depositor's proof (`spend_bound_to_adapt`) keeps another caller from redirecting it; `PoolCall` does not show the binding, because the pool's `Step` hides its arguments.
- **D7. The environment rule.** The pool's `Step` does not name its caller. `OtherUserStep` states the owner-binding consequence as the rule for every other pool user: it spends no note keyed to the adjudicator.
- **D8. Status per token.** Ruling 6 makes each token an independent copy, so each token has its own channel status, and a challenge is per token. go-nitro shares one status across assets.
- **D9. "Paid" means "credited".** A participant's balance is the value of the payment notes the adjudicator created for it (`Holder.payments`), not the value still unspent (audit A11). The payee alone can spend them (`Config.payeeKey_user`, pool `transact_spends_only_owned`).
- **D10. The payout amount is in the call.** The transfer label carries `x`, because the pool proof fixes its output values. The adjudicator requires `x` to equal the affordable amount (go-nitro), not `x ≤` the affordable amount (Nitro `T(A, B, x)`). The second rule removes F1's credit case but has no Nitro step to refine to.
- **D11. Deposit details.** The `merged` list may be empty, and the deposit amount may be 0, as in Nitro. An honest depositor that merges nothing cannot be made stale by another deposit's merge.
- **D12. Deployment.** The adjudicator is deployed into any reachable pool state at time 0 (`genesis`, `ArmadaReachable`).

## General lemmas and Mathlib

No hand-written general lemma: every theorem statement names a project type. Mathlib and core definitions used: `Relation.ReflTransGen` (Mathlib, for `ArmadaReachable`), `List.Perm`, `List.Nodup`, `List.sum`, `List.flatten`, `List.lookup`, `List.eraseDups`, `List.filter` (core).

## Checks

- `lake build`: exit 0.
- `grep -rnE 'holdings|bytes32|2 *\^ *160|finalizesAt|stateHash|outcomeHash|indices|configuredAssets' ArmadaLean/ArmadaNitro` prints one line, the comment in `State.lean` that explains the absence of a `holdings` table.
- No `axiom` under `ArmadaLean/ArmadaNitro/`. Each file sets `autoImplicit false`. `#print axioms` on `step_refines`, `pending_payout_not_blocked` and `satp_theorem_3_2_notes` lists `EdDSAVerify` (the pool's primitive, through `Step`), `propext` and `sorryAx`.
- The `theorem` statements outside `ArmadaLean/ArmadaNitro/` are identical to `c5d87d2` (251 statements, empty diff). The only change outside `ArmadaNitro/` is 8 import lines in `ArmadaLean.lean`.
