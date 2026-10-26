# Nitro theorems: property map

This file maps the 189 prose properties of `armada-laconic/notes/statement-audit-2026-10-25/` (S1 ForceMove 2018, S2 Nitro 2019, S3 SATP 2022, S4 docs.statechannels.org) to the Lean declarations under `ArmadaLean/Nitro/`. Every theorem has proof `sorry`. The statements are the deliverable.

## Modules

| Module | Content |
|---|---|
| `ArmadaLean/Nitro/Address.lean` | coins, time, participants, fixed part, addresses, balances (S2 §3.1) |
| `ArmadaLean/Nitro/Outcome.lean` | items, allocations, priority payout, afford, reprioritize, outcomes (S2 §5.1, §6.1; S3 §2.4) |
| `ArmadaLean/Nitro/Channel.lean` | states, signed states, application rules, ForceMove and consensus rules, channel status and modes |
| `ArmadaLean/Nitro/Adjudicator.lean` | the adjudicator state and the operations deposit, withdraw, transfer, claim, reclaim, challenge, respond, conclude, tick; `Step`, `Reachable` |
| `ArmadaLean/Nitro/Strategy.lean` | network states, moves, threat model, `Assumptions`, `Unbeatable`, `Prevents`, finalizable, enabled, funded, value (S2 §4) |
| `ArmadaLean/Nitro/Value.lean` | outcome network, DAG, Turbo Value Algorithm, Minimum Payout Calculation, Nitro Lower-bound Value Algorithm (S2 §5.2, §6.2) |
| `ArmadaLean/Nitro/Constructions.lean` | ledger channels with sub-channels and the virtual channel construction (S2 §5.3-5.4, §6.3-6.5) |
| `ArmadaLean/Nitro/SATP.lean` | vouchers, the virtual channel rules, routes, Protocols 3.1-3.3 state (S3 §3, Appendix A) |
| `ArmadaLean/Nitro/Safety.lean` | 54 theorems: on-chain safety, conservation, data operations |
| `ArmadaLean/Nitro/Liveness.lean` | 46 theorems: unbeatable strategies, value algorithms, constructions, SATP Lemma 3.1 and Theorem 3.2 |

## Modelling choices the papers do not force

- Single asset. S2:142-148 treats one asset. S3 and S4 handle many. The model is one single-asset instance; a multi-asset adjudicator is a family of independent instances, because no operation in S1-S3 moves value between assets.
- Two guarantee forms. S2 §6.1 makes a guarantee the outcome of a whole channel (`Outcome.guarantee target priority`, used by `claim`). S3:322-323 makes a guarantee an item inside an allocation (`Item.guarantee x [left, right]`, used by `reclaim`). Both are modelled; they are not unified.
- Symbolic hash and signatures. A channel address is the constructor `Address.channel` applied to the fixed part, so injectivity holds by construction. A signed state carries the list of signers. Who can produce a signature is the game rule `Assumptions.unforgeable`.
- Fixed part. S3:198-203 (peers, appDef, nonce, challengeDuration) is the superset of S1:600-605 and S2:155-157, so it is the fixed part for all sources.
- Conclusion proof. S1:1030-1058 uses n consecutive conclude moves. S2:297-299 and S3:286-289 use one final state supported by all. The model uses the S2/S3 form.
- Challenge precondition. S1:1341-1342 forbids a challenge while one is in progress. S3 Listing 1 (`isOpen`, `version >=`) would allow a re-challenge at an equal version during an active challenge, which lets an adversary push the deadline forever. The model follows S1. S3-14 records this.
- Respond. `respond` is S1 `respondWithMove`/`refute` generalized to any supported state with a higher turn number (S1:1377-1381). It also works on an open channel, where it only raises the stored turn number (S1:1543-1545). S4 names that case `checkpoint`.
- Channel status. `ChannelStatus` has explicit constructors `open`, `challenged`, `finalized`. The timeout is passive: `mode` compares the deadline with `now`. There is no time sentinel.
- Applications. The deployed applications are a function `Apps := AppId → Rules`. `Rules.supports` is a `Prop`; the operations that read it are `noncomputable` and decide it classically.
- The game. S2:460-461: one adversary controls every other participant. One round of `Unbeatable` is: any finite feasible adversary prefix, then one honest move. This is front-running (S2:540-542). `Assumptions.unimpeded` forbids the adversary to move the clock to a pending deadline of the honest participant (S2:537-539, S3:166-167). Only the honest `wait` reaches a deadline. `Unbeatable` is an inductive (finite) strategy tree. `Prevents` is a safety property over `Run`s, used for enabled outcomes.
- DAG. "The network is a DAG" is "a topological ordering exists" (`Adjudicator.IsDAG`), following S2:796-799.
- Minimum Payout Calculation. S2:1202-1244 gives a constrained optimization. The model defines the minimum semantically: the least amount a destination receives over all exhausted claim orders inside the group (`GuaranteeGroup.IsMinPayout`). The lower-bound algorithm takes any function that meets it (`MinPayoutCorrect`).
- Allocation `+=` on a missing key (S3:358-359). `Allocation.addTo` appends an entry `A(x)` at the end when the destination is absent.
- SATP app data. `Decode : Nat → VirtualAppData` is the parse of `appData` (S3:209). The virtual channel rules take it as a parameter.
- Deposit and withdraw come from S2 §3.1 (S3:764-768 defers them).
- Every `theorem` has proof `sorry`, including the ones a one-line proof would close, so that the sorry count equals the theorem count.

## Property map (189 ids)

Disposition forms: `theorem NAME`, `definition NAME`, `assumption field NAME`, `superseded-by ID`, `out of scope: reason`.

| Id | Disposition |
|---|---|
| S1-D01 | definition FixedPart, FixedPart.address |
| S1-D02 | theorem channel_address_inj, channel_address_ne_participant |
| S1-D03 | definition Outcome, Allocation |
| S1-D04 | definition SignedState |
| S1-D05 | definition State, State.mover |
| S1-D06 | theorem mover_determined_by_turn, mover_cyclic |
| S1-D07 | definition State (field appData) |
| S1-D08 | definition State (field isFinal, the S3 form of the conclude state type) |
| S1-D09 | superseded-by S2-23 (definition AtFundingPoint) |
| S1-D10 | superseded-by S2-23 (definition AtFundingPoint) |
| S1-D11 | definition Mode, ChannelStatus.mode |
| S1-D12 | definition Challenge, ChannelStatus.mode; theorem challenge_in_progress_before_deadline, timeout_finalizes |
| S1-D13 | definition Op |
| S1-A01 | theorem forceMove_supports_valid_run |
| S1-A02 | theorem forceMove_supports_valid_run (definition UniversalTransition) |
| S1-A03 | definition ValidMove, ConclusionTransition (the per-type dispatch folds into one predicate) |
| S1-A04 | theorem forceMove_conclude_keeps_outcome, conclude_moves_no_value |
| S1-A05 | theorem forceMove_conclude_keeps_outcome |
| S1-A06 | superseded-by S2-23 (hypothesis SetupPhaseKeepsOutcome in funding_point_universally_finalizable) |
| S1-A07 | superseded-by S2-23 (hypothesis SetupPhaseKeepsOutcome in funding_point_universally_finalizable) |
| S1-A08 | theorem forceMove_conclude_keeps_outcome |
| S1-A09 | theorem conclude_consensus_needs_all (definition ConclusionProof, the S2/S3 form) |
| S1-A10 | theorem challenge_requires, challenge_can_happen |
| S1-A11 | theorem respond_requires, respond_can_happen (refute and respond are one operation; S1 marks it superseded) |
| S1-A12 | theorem respond_requires, respond_can_happen |
| S1-A13 | superseded-by S1-A12 (Nitro has no alternative moves; one supported candidate responds) |
| S1-A14 | theorem conclude_can_happen, finalized_permanent |
| S1-A15 | theorem transfer_requires_finalized |
| S1-A16 | theorem payout_priority_formula |
| S1-A17 | superseded-by S2-02 (definition Adjudicator.statusOf: one contract, many channels) |
| S1-A18 | theorem respond_can_happen |
| S1-A19 | definition Rules (pure by construction: the rules read only states) |
| S1-A20 | theorem failed_op_no_effect |
| S1-A21 | theorem turnNumRecord_monotone, challenge_requires |
| S1-B01 | theorem directly_funded_pays, latest_state_finalizable |
| S1-B02 | theorem respond_requires, turnNumRecord_monotone |
| S1-B03 | theorem timeout_finalizes |
| S1-B04 | theorem respond_can_happen |
| S1-B05 | theorem late_observer_can_respond |
| S1-B06 | theorem funding_point_universally_finalizable |
| S1-B07 | theorem payout_earlier_paid_in_full |
| S1-C01 | theorem deposit_can_happen |
| S1-C02 | theorem challenge_can_happen |
| S1-C03 | theorem transfer_can_happen |
| S1-E01 | out of scope: app-specific game logic (S1:536-551 Specification 1 is a payment-game library rule, not an adjudicator rule) |
| S1-E02 | out of scope: app design incentive (S1:339-346 commit-reveal default winner is a game-library choice) |
| S1-E03 | superseded-by S1-A12 (alternative moves are dropped; S1:781-797) |
| S1-E04 | out of scope: participant behaviour (S1:1187-1196 rational backing out is a choice, not a guarantee) |
| S1-E05 | out of scope: economic limit (S1:1566-1586: griefing cannot be eliminated; the deposit extension is optional and not a claim of the protocol) |
| S1-F01 | definition Address (the hash is a constructor; theorem channel_address_inj) |
| S1-F02 | assumption field Assumptions.unforgeable |
| S1-F03 | definition Adjudicator.tick, Challenge (field deadline) |
| S1-F04 | theorem held_eq_total_balances |
| S1-F05 | theorem funding_decoupled_from_rules |
| S2-01 | theorem balances_absent_zero (definition Balances.get) |
| S2-02 | definition FixedPart.address; theorem channel_address_inj |
| S2-03 | assumption field Assumptions.unforgeable (the channel-address half holds by construction of Address) |
| S2-04 | theorem deposit_can_happen |
| S2-05 | theorem deposit_effects, held_eq_total_balances |
| S2-06 | theorem withdraw_requires_key, withdraw_effects |
| S2-07 | theorem withdraw_leaves_channels |
| S2-08 | theorem held_eq_total_balances, redistribution_conserves_total, held_changes_only_by_deposit_withdraw |
| S2-09 | definition Allocation, Entry |
| S2-10 | theorem transfer_requires_finalized |
| S2-11 | theorem finalized_two_ways |
| S2-12 | theorem challenge_can_happen, timeout_finalizes, latest_state_finalizable |
| S2-13 | theorem conclude_can_happen, conclusion_proof_finalizable |
| S2-14 | theorem finalized_permanent, finalized_outcome_only_redistributed |
| S2-15 | theorem redistribution_ignores_caller |
| S2-16 | theorem directly_funded_pays |
| S2-17 | definition FundedFor, Adjudicator.DirectlyFunded |
| S2-18 | definition Value; theorem turbo_value_is_value |
| S2-19 | assumption field Assumptions.unimpeded |
| S2-20 | definition Unbeatable (front-running is the adversary prefix in Unbeatable.move) |
| S2-21 | definition Finalizable; theorem finalizable_funded_pays |
| S2-22 | theorem finalizable_unique, channel_finalizability_cases |
| S2-23 | theorem funding_point_universally_finalizable, concluded_universally_finalizable |
| S2-24 | definition Enabled; theorem finalizable_or_two_enabled, single_enabled_is_finalizable, finalizable_is_enabled |
| S2-25 | definition Allocation.dedup; theorem paidTo_first_entry_only |
| S2-26 | theorem payout_priority_formula, payout_bounded |
| S2-27 | definition Allocation.Affords; theorem affords_when_fully_funded |
| S2-28 | theorem transfer_effects, reduceOwed_owed, transfer_can_happen |
| S2-29 | theorem transfer_fails_when_unaffordable |
| S2-30 | theorem turbo_redistribution_unbeatable |
| S2-31 | theorem deposit_bounds_value, withdrawal_affects_only_owner (definition Threat.TransfersOnly) |
| S2-32 | definition Adjudicator.IsDAG; theorem participant_can_prevent_cycles |
| S2-33 | definition Adjudicator.turboValue |
| S2-34 | theorem turbo_value_upper_bound |
| S2-35 | theorem turbo_value_achievable |
| S2-36 | theorem turbo_order_independent, turbo_value_order_choice_irrelevant |
| S2-37 | theorem ledger_offload_funds_subchannel |
| S2-38 | definition Outcome, Op |
| S2-39 | definition Outcome (constructor guarantee); theorem reprioritize_keeps_amounts |
| S2-40 | theorem claim_requires |
| S2-41 | definition Allocation.reprioritize; theorem reprioritize_example, reprioritize_keeps_amounts |
| S2-42 | definition GuaranteeAffords |
| S2-43 | theorem claim_effects, claim_fails_otherwise |
| S2-44 | theorem claim_order_dependent |
| S2-45 | definition Adjudicator.nitroValue, GuaranteeGroup.IsMinPayout; theorem nitro_lower_bound_achievable, nitro_lower_bound_underestimates, figure23_lower_bound |
| S2-46 | theorem overfunded_min_payout, fully_funded_min_payout, single_guarantee_determined |
| S2-47 | theorem end_participant_offloads |
| S2-48 | theorem intermediary_recovers_collateral |
| S2-49 | theorem consensus_enabled_outcomes, subchannel_open_value_preserving, subchannel_close_value_preserving, ledger_topup_reorder_safe, ledger_topup_deposit_funds, ledger_partial_withdrawal, virtual_open_value_preserving, virtual_close_value_preserving |
| S3-01 | definition FixedPart |
| S3-02 | definition State |
| S3-03 | definition State (FixedPart plus the variable fields) |
| S3-04 | definition ChannelStatus, Adjudicator.statusOf |
| S3-05 | definition FixedPart.address; theorem channel_address_inj |
| S3-06 | definition SupportProof |
| S3-07 | definition Rules |
| S3-08 | definition consensusRules; theorem conclude_consensus_needs_all |
| S3-09 | definition Item (constructor alloc) |
| S3-10 | definition Item (constructor guarantee) |
| S3-11 | definition Item.amount |
| S3-12 | definition Allocation; theorem payout_priority_formula |
| S3-13 | definition ChannelStatus.IsOpen; theorem isOpen_iff |
| S3-14 | theorem challenge_requires, challenge_can_happen (choice: S1 forbids a challenge while one is in progress; S3 Listing 1 would allow it) |
| S3-15 | theorem reclaim_requires, reclaim_effects, reclaim_can_happen |
| S3-16 | theorem finalized_two_ways, conclude_can_happen, withdraw_requires_key |
| S3-17 | definition satpVirtualRules |
| S3-18 | definition ValidateOutcomeChange |
| S3-19 | theorem satp_outcome_change_keeps_total |
| S3-20 | theorem satp_theorem_3_2, satp_intermediary_before_round2, satp_end_user_recovers, satp_reclaim_credits_intermediary |
| S3-21 | theorem satp_lemma_3_1, satp_peers_can_finalize |
| S3-22 | out of scope: gas cost and wall-clock bound (S3:491-493 Theorem 3.1); the model has no cost or duration measure |
| S3-23 | out of scope: conjecture (S3:451-452 Conjecture 3.1 is stated, not claimed proved) |
| S3-24 | assumption field Assumptions.unimpeded |
| S3-25 | assumption field Assumptions.unforgeable |
| S3-26 | superseded-by S2-04 (S3:764-768 defers deposits and withdrawals; the model takes them from S2 §3.1) |
| S4-0010-01 | definition FixedPart, State |
| S4-0010-02 | theorem channel_address_inj |
| S4-0010-03 | out of scope: S4-only contract encoding (stateHash); the model stores values, not hashes |
| S4-0010-04 | out of scope: S4-only contract encoding (signedBy bitmask); definition SignedState carries the signer list |
| S4-0030-01 | out of scope: S4-only multi-asset exit encoding; the model is one single-asset instance (S2:142-148) |
| S4-0030-02 | out of scope: S4-only allocationType and metadata encoding; definition Item carries the two kinds |
| S4-0030-03 | theorem transfer_effects (S2-28 supports it) |
| S4-0030-04 | theorem reclaim_requires, transfer_effects (S3-15 supports it; a transfer reads an allocation only) |
| S4-0030-05 | out of scope: S4-only 32-byte destination encoding; definition Address has the two kinds |
| S4-0040-01 | definition Mode |
| S4-0040-02 | definition ChannelStatus.mode (S3-13 supports it; the zero sentinel is S4-only) |
| S4-0040-03 | out of scope: S4-only reset of the stored turn to 0 on conclude; S1-S3 do not state it (the monotone half is theorem turnNumRecord_monotone) |
| S4-0040-04 | out of scope: S4-only storage packing; the model stores the status as a value |
| S4-0040-05 | theorem timeout_finalizes, tick_moves_only_time |
| S4-0020-01 | definition consensusRules |
| S4-0010-05 | theorem conclude_can_happen |
| S4-0060-01 | out of scope: S4-only; S2:227-228 says "Anyone can deposit into an address of either type" |
| S4-0060-02 | out of scope: S4-only expectedHeld check; S1-S3 state the deposit-order rule as the payout priority, theorem payout_earlier_paid_in_full |
| S4-0060-03 | theorem deposit_effects |
| S4-0070-01 | theorem conclude_consensus_needs_all |
| S4-0070-02 | theorem challenge_requires |
| S4-0070-03 | theorem turnNumRecord_monotone, challenge_requires, respond_requires |
| S4-0070-04 | theorem finalized_two_ways |
| S4-0080-01 | theorem transfer_requires_finalized, reclaim_requires |
| S4-0080-02 | out of scope: S4-only stored-hash matching; the model stores the outcome value |
| S4-0080-03 | theorem payout_bounded, transfer_effects |
| S4-0070-05 | theorem conclusion_proof_finalizable, directly_funded_pays |
| S4-0070-06 | theorem latest_state_finalizable |
| S4-C-01 | theorem held_eq_total_balances |
| S4-C-02 | out of scope: Armada note-pool encoding; not in S1-S3 |
| S4-0070-07 | theorem conclude_moves_no_value |
| S4-0080-04 | theorem transfer_effects (the transfer pays exactly x) |
| S4-0060-04 | theorem deposit_can_happen |
| S4-0060-05 | theorem deposit_effects, ledger_topup_deposit_funds |
| S4-0070-08 | theorem challenge_can_happen |
| S4-0040-06 | theorem timeout_finalizes |
| S4-0070-09 | theorem conclude_can_happen |
| S4-0080-06 | theorem transfer_can_happen |
| S4-0080-05 | theorem reclaim_can_happen, reclaim_effects |
| S4-0070-10 | theorem respond_can_happen |
| S4-0010-06 | out of scope: S4-only client check on the participant list |
| S4-0010-07 | theorem channel_address_inj (S1-D02 supports it) |
| S4-0010-08 | out of scope: S4-only parameter bound; the theorems take 0 < challengeDuration as a hypothesis |
| S4-0010-09 | out of scope: S4-only overflow bound; S2:144 takes quantities with no maximum |
| S4-0010-10 | out of scope: S4-only client behaviour (stop executing after isFinal) |
| S4-0020-02 | definition Rules |
| S4-0020-03 | definition satpVirtualRules (S3 Appendix A) |
| S4-0040-07 | out of scope: S4-only client lifecycle states; the on-chain modes are definition Mode |
| S4-0040-08 | superseded-by S2-17 (definition FundedFor) |
| S4-0040-09 | out of scope: S4-only client behaviour (when to fund and defund) |
| S4-0040-10 | superseded-by S2-23 (theorem funding_point_universally_finalizable) |
| S4-0060-06 | theorem payout_earlier_paid_in_full (S1-B07 supports it) |
| S4-0060-07 | theorem ledger_offload_funds_subchannel, subchannel_open_value_preserving |
| S4-0060-08 | theorem end_participant_offloads (S2-47 construction) |
| S4-0060-09 | out of scope: S4-only ETH/ERC20 chain mechanics |
| S4-0070-11 | theorem respond_can_happen (S1-A12 supports the respond half; the event-caching half is S4-only client infrastructure) |
| S4-0070-12 | out of scope: S4-only client infrastructure; the model stores values, not hashes |
| S4-0080-07 | theorem subchannel_close_value_preserving, virtual_close_value_preserving |
| S4-0080-08 | theorem ledger_offload_funds_subchannel, end_participant_offloads |
| S4-0080-09 | out of scope: S4-only client tracking of events |

### Counts per disposition

- assumption: 5
- definition: 50
- out of scope: 26
- superseded-by: 10
- theorem: 98
- total: 189

## Theorems (100)

| Theorem | Module | Meaning | Property ids | Source |
|---|---|---|---|---|
| `channel_address_inj` | `Safety.lean` | One address names one channel. | S1-D02, S1-F01, S2-02, S2-03, S3-05, S4-0010-02 | S1:610-611 |
| `channel_address_ne_participant` | `Safety.lean` | A channel address is never a participant address. | S1-D02, S2-02 | S4 |
| `balances_absent_zero` | `Safety.lean` | An absent address has balance zero. | S2-01 | S2:162-163 |
| `held_eq_total_balances` | `Safety.lean` | Coins held equal the sum of balances on every reachable state. | S1-F04, S2-05, S2-08, S4-C-01 | S2:230-231 |
| `deposit_effects` | `Safety.lean` | A deposit adds exactly x to one balance and to the coins held. | S1-C01, S2-04, S2-05, S4-0060-03, S4-0060-04, S4-0060-05 | S2:165-168 |
| `deposit_can_happen` | `Safety.lean` | Any caller can deposit to any address. | S2-04 | S2:166-167 |
| `withdraw_requires_key` | `Safety.lean` | A withdrawal is by the owner and within the balance. | S2-06, S2-07, S3-16 | S2:227-229 |
| `withdraw_effects` | `Safety.lean` | A withdrawal removes x from the owner and from the coins held. | S2-06 | S2:169-170 |
| `withdraw_leaves_channels` | `Safety.lean` | A withdrawal never moves a channel balance. | S2-07 | S2:227-229 |
| `payout_priority_formula` | `Safety.lean` | Entry k is paid min(owed, held - total owed before k). | S1-A16, S1-B07, S2-26, S3-12, S4-0080-03 | S1:1837-1853 |
| `payout_earlier_paid_in_full` | `Safety.lean` | If a later entry is paid, every earlier entry is paid in full. | S1-B07, S2-26 | S1:1812-1821 |
| `payout_bounded` | `Safety.lean` | The payout never exceeds the coins held or an entry amount. | S2-26, S2-28 | S4 |
| `paidTo_first_entry_only` | `Safety.lean` | A destination is paid at most its first entry. | S2-25 | S2:744-746 |
| `affords_when_fully_funded` | `Safety.lean` | A fully funded allocation affords every entry in full. | S2-16, S2-27 | S2:749-751 |
| `transfer_effects` | `Safety.lean` | The three effects of an affordable transfer; no coin leaves. | S1-A15, S2-10, S2-28, S4-0080-03, S4-0080-04 | S2:765-770 |
| `reduceOwed_owed` | `Safety.lean` | Reducing an owed amount is exact and local. | S2-28, S2-43 | S4 |
| `transfer_can_happen` | `Safety.lean` | An affordable transfer on a finalized allocation succeeds, exact result. | S2-15, S2-28 | S2:765-767 |
| `transfer_fails_when_unaffordable` | `Safety.lean` | An unaffordable transfer fails and changes nothing. | S1-A20, S2-29 | S2:771-772 |
| `transfer_requires_finalized` | `Safety.lean` | A transfer succeeds only on a finalized channel. | S1-A15, S2-10, S3-16, S4-0080-01 | S2:261-266 |
| `redistribution_ignores_caller` | `Safety.lean` | Transfer, claim and reclaim give the same result for every caller. | S2-15 | S2:312-313 |
| `redistribution_conserves_total` | `Safety.lean` | Redistribution keeps the sum of balances and the coins held. | S2-08 | S4 |
| `finalized_two_ways` | `Safety.lean` | A finalized outcome came from a conclude or a timed-out challenge. | S1-A14, S1-B03, S2-11, S3-16, S4-0070-04 | S2:770 |
| `finalized_permanent` | `Safety.lean` | A finalized channel stays finalized. | S1-A14, S1-D12, S2-14 | S2:301-302 |
| `finalized_outcome_only_redistributed` | `Safety.lean` | A finalized outcome is only ever redistributed, never replaced. | S2-14 | S4 |
| `challenge_requires` | `Safety.lean` | A challenge needs a participant caller, an open channel, support and a turn >= record. | S1-A10, S1-A21, S3-14, S4-0070-02, S4-0070-03 | S1:1340-1354 |
| `challenge_can_happen` | `Safety.lean` | A valid challenge succeeds with deadline now + duration, exact result. | S1-A10, S1-C02, S1-F03, S2-12, S3-14, S4-0070-08 | S1:1353 |
| `challenge_effects` | `Safety.lean` | A fresh challenge puts the channel in challenge mode and moves no coins. | S1-B04, S1-D12, S3-14 | S4 |
| `respond_requires` | `Safety.lean` | A response needs a non-finalized channel, support and a higher turn. | S1-A11, S1-A12, S1-A13, S1-A21, S1-B02 | S1:1431-1440 |
| `respond_can_happen` | `Safety.lean` | A valid response reopens the channel at the new turn. | S1-A18, S1-A21, S1-B04, S4-0070-10 | S1:1266-1269 |
| `turnNumRecord_monotone` | `Safety.lean` | No step lowers the stored turn number. | S1-A21, S1-B02, S4-0040-03, S4-0070-03 | S1:1543-1545 |
| `conclude_requires` | `Safety.lean` | A conclude needs a non-finalized channel, support and isFinal. | S1-A14, S2-13, S3-16, S4-0010-05, S4-0070-01 | S1:1495-1500 |
| `conclude_can_happen` | `Safety.lean` | A valid conclude finalizes at once with the candidate outcome. | S1-A14, S2-13, S3-16, S4-0070-09 | S1:1507 |
| `conclude_moves_no_value` | `Safety.lean` | A conclude moves no coins and no time. | S1-A04, S1-A05, S4-0070-07 | S1:976-980 |
| `conclude_consensus_needs_all` | `Safety.lean` | Under the consensus app a conclude carries one state signed by all. | S1-A09, S2-13, S3-08, S3-16, S4-0020-01, S4-0070-01 | S2:297-298 |
| `timeout_finalizes` | `Safety.lean` | A challenge past its deadline is finalized with the challenge outcome. | S1-B03, S1-D12, S2-12, S4-0040-05, S4-0040-06 | S1:1260-1265 |
| `challenge_in_progress_before_deadline` | `Safety.lean` | A challenge before its deadline is in progress with no final outcome. | S1-D12 | S1:1295 |
| `tick_moves_only_time` | `Safety.lean` | The clock changes no balance and no status. | S1-F03, S4-0040-05 | S4 |
| `failed_op_no_effect` | `Safety.lean` | A failed operation leaves the chain unchanged. | S1-A20 | S1:685-686 |
| `funding_decoupled_from_rules` | `Safety.lean` | The dispute operations do not read the balances. | S1-F05 | S1:1609-1628 |
| `forceMove_supports_valid_run` | `Safety.lean` | A ForceMove support proof is a run of n valid moves signed by movers. | S1-A01, S1-A02, S1-A03, S1-D04, S1-D05, S1-D06 | S1:744-751 |
| `forceMove_conclude_keeps_outcome` | `Safety.lean` | A ForceMove conclude transition keeps the outcome; conclude is absorbing. | S1-A04, S1-A05, S1-A08 | S1:976-980 |
| `mover_determined_by_turn` | `Safety.lean` | The mover is a function of channel and turn number. | S1-D05, S1-D06 | S1:724-727 |
| `mover_cyclic` | `Safety.lean` | Turns cycle with period n. | S1-D06 | S1:725-727 |
| `claim_requires` | `Safety.lean` | A claim needs a finalized guarantee, a finalized target and affordability. | S2-40, S2-42, S2-43 | S2:1139-1141 |
| `claim_effects` | `Safety.lean` | The three effects of an affordable claim; no coin leaves. | S2-43 | S2:1141-1144 |
| `claim_fails_otherwise` | `Safety.lean` | A claim that is not affordable has no effect. | S2-40, S2-43 | S2:1145 |
| `reprioritize_example` | `Safety.lean` | The S2 example (L|A,B,C) on (C:1,D:2,A:4) gives (A:4,C:1,D:2). | S2-41 | S2:1099-1101 |
| `reprioritize_keeps_amounts` | `Safety.lean` | Reprioritization keeps amounts and puts listed addresses first. | S2-39, S2-41 | S2:1098-1099 |
| `reclaim_requires` | `Safety.lean` | A reclaim needs both channels finalized and a guarantee entry. | S3-15 | S3:348-352 |
| `reclaim_effects` | `Safety.lean` | A reclaim credits left and right from the target and deletes the guarantee. | S3-15, S4-0080-05 | S3:358-363 |
| `reclaim_can_happen` | `Safety.lean` | A reclaim with its preconditions succeeds, exact result. | S3-15, S4-0080-05 | S4 |
| `isOpen_iff` | `Safety.lean` | isOpen means open or challenge mode. | S3-13, S4-0040-02 | S3:294-298 |
| `mode_of_absent` | `Safety.lean` | A channel with no record is open at turn 0. | S1-D11, S2-11 | S4 |
| `held_changes_only_by_deposit_withdraw` | `Safety.lean` | Only deposit and withdraw change the coins held. | S2-05, S2-08 | S4 |
| `directly_funded_pays` | `Liveness.lean` | A directly funded finalized allocation pays p its entry with no wait. | S1-A06, S1-A07, S1-B01, S1-C03, S2-16, S2-21, S2-31, S4-0070-05, S4-0080-06 | S2:779-781 |
| `finalizable_funded_pays` | `Liveness.lean` | A finalizable allocation in a channel funded for p pays p its entry. | S2-16, S2-17, S2-21 | S2:480-481 |
| `conclusion_proof_finalizable` | `Liveness.lean` | A held conclusion proof makes its outcome finalizable with no wait. | S1-A14, S2-13, S2-21, S2-23, S4-0070-05 | S2:296-299 |
| `latest_state_finalizable` | `Liveness.lean` | The latest supported state is finalizable by challenge and timeout. | S1-B01, S1-B03, S1-C02, S2-12, S4-0070-06 | S2:292-296 |
| `late_observer_can_respond` | `Liveness.lean` | A participant with a higher supported state can reopen a challenged channel. | S1-B05 | S1:1511-1529 |
| `finalizable_unique` | `Liveness.lean` | Two participants cannot each force different outcomes of one channel. | S2-22 | S2:612-614 |
| `channel_finalizability_cases` | `Liveness.lean` | A channel is in one of the four finalizability cases. | S2-22 | S2:597-611 |
| `finalizable_or_two_enabled` | `Liveness.lean` | A participant has a finalizable outcome or two enabled outcomes. | S2-24 | S2:653-656 |
| `single_enabled_is_finalizable` | `Liveness.lean` | A single enabled outcome is finalizable. | S2-24 | S2:657-658 |
| `finalizable_is_enabled` | `Liveness.lean` | A finalizable outcome is enabled. | S2-21, S2-24 | S4 |
| `funding_point_universally_finalizable` | `Liveness.lean` | At the funding point the outcome is universally finalizable. | S1-A06, S1-A07, S1-B06, S2-23 | S2:635-636 |
| `concluded_universally_finalizable` | `Liveness.lean` | A concluded outcome is universally finalizable. | S1-A14, S2-23 | S2:637-640 |
| `consensus_enabled_outcomes` | `Liveness.lean` | During a consensus transition only the old and new outcomes are enabled. | S2-49, S3-08, S4-0020-01 | S2:660-688 |
| `turbo_redistribution_unbeatable` | `Liveness.lean` | In Turbo any transfer strategy that works is unbeatable. | S2-16, S2-30 | S2:775-777 |
| `deposit_bounds_value` | `Liveness.lean` | A deposit of y changes a value by between 0 and y. | S2-31 | S2:785-787 |
| `withdrawal_affects_only_owner` | `Liveness.lean` | A withdrawal by another participant leaves p's value unchanged. | S2-31 | S2:787-789 |
| `participant_can_prevent_cycles` | `Liveness.lean` | A participant can keep the outcome network acyclic. | S2-32 | S2:792-794 |
| `turbo_value_upper_bound` | `Liveness.lean` | No strategy obtains more than the Turbo Value Algorithm gives. | S2-32, S2-33, S2-34 | S2:836-837 |
| `turbo_value_achievable` | `Liveness.lean` | The Turbo Value Algorithm value is obtainable. | S2-18, S2-33, S2-35 | S2:837-839 |
| `turbo_value_is_value` | `Liveness.lean` | The Turbo Value Algorithm computes the value of a network state. | S2-18, S2-33, S2-34, S2-35 | S2:482-484 |
| `turbo_order_independent` | `Liveness.lean` | Exhausted transfer sequences give the same balances. | S2-36 | S2:842-843 |
| `turbo_value_order_choice_irrelevant` | `Liveness.lean` | The topological order chosen does not change the value. | S2-33, S2-36 | S2:819 |
| `ledger_offload_funds_subchannel` | `Liveness.lean` | A ledger channel funds its sub-channel for both participants. | S2-37, S4-0060-07, S4-0080-08 | S2:859-865 |
| `subchannel_open_value_preserving` | `Liveness.lean` | Opening a sub-channel preserves value. | S2-49, S4-0060-07 | S2:891-922 |
| `subchannel_close_value_preserving` | `Liveness.lean` | Closing a sub-channel preserves value. | S2-49, S4-0080-07 | S2:939-957 |
| `ledger_topup_reorder_safe` | `Liveness.lean` | Moving A to the end of an underfunded ledger pays A the same. | S2-49, S4-0060-05 | S2:959-995 |
| `ledger_topup_deposit_funds` | `Liveness.lean` | After the top-up deposit every entry is affordable in full. | S2-04, S2-49 | S2:989-995 |
| `ledger_partial_withdrawal` | `Liveness.lean` | A partial withdrawal pays A with no wait and funds the new ledger. | S2-49 | S2:997-1047 |
| `claim_order_dependent` | `Liveness.lean` | Claim order can change who is paid. | S2-44 | S2:1148-1151 |
| `nitro_lower_bound_achievable` | `Liveness.lean` | The Nitro lower-bound value is obtainable. | S2-18, S2-45 | S2:1152-1154 |
| `nitro_lower_bound_underestimates` | `Liveness.lean` | The lower-bound algorithm strictly underestimates in some case. | S2-45 | S2:1194-1196 |
| `overfunded_min_payout` | `Liveness.lean` | An overfunded group pays every destination in full. | S2-46 | S2:1216-1218 |
| `fully_funded_min_payout` | `Liveness.lean` | A fully funded group pays every destination in full. | S2-46 | S2:1251-1253 |
| `single_guarantee_determined` | `Liveness.lean` | With one guarantee the payouts are fully determined. | S2-46 | S2:1253-1255 |
| `figure23_lower_bound` | `Liveness.lean` | In Figure 23, I gets 5 and A, B have lower bound 0. | S2-44, S2-45 | S2:1173-1176 |
| `end_participant_offloads` | `Liveness.lean` | A or B can offload the virtual channel. | S2-37, S2-47, S4-0060-08 | S2:1299-1316 |
| `intermediary_recovers_collateral` | `Liveness.lean` | The intermediary can offload the virtual channel and recover x. | S2-48 | S2:1317-1343 |
| `virtual_open_value_preserving` | `Liveness.lean` | Opening a virtual channel preserves value. | S2-49, S4-0060-08 | S2:1364-1394 |
| `virtual_close_value_preserving` | `Liveness.lean` | Closing a virtual channel preserves value. | S2-49, S4-0080-07 | S2:1412-1431 |
| `satp_outcome_change_keeps_total` | `Liveness.lean` | validateOutcomeChange keeps the funded total of the start state. | S3-18, S3-19 | S3:707-709 |
| `satp_lemma_3_1` | `Liveness.lean` | Lemma 3.1: V finalizes at version 0 with the original outcome or with the same total. | S3-19, S3-21 | S3:511-513 |
| `satp_peers_can_finalize` | `Liveness.lean` | Lemma A.1: a peer can force V to finalize with the same total. | S3-21 | S3:747-750 |
| `satp_theorem_3_2` | `Liveness.lean` | Theorem 3.2: an honest intermediary recovers its ledger balances. | S3-20 | S3:503-507 |
| `satp_intermediary_before_round2` | `Liveness.lean` | Theorem 3.2 Cases 1-2: before Round 2 the intermediary keeps its balances. | S3-20 | S3:522-537 |
| `satp_end_user_recovers` | `Liveness.lean` | The end-user analogue of Theorem 3.2 for Alice. | S3-20 | S3:500-501 |
| `satp_reclaim_credits_intermediary` | `Liveness.lean` | Two reclaims credit the intermediary with a + b and delete the guarantees. | S3-15, S3-20 | S3:484-485 |
