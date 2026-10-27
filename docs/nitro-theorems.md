# Nitro theorems: property map

This file maps the 189 prose properties of `armada-laconic/notes/statement-audit-2026-10-25/` to the Lean declarations under `ArmadaLean/Nitro/`. The 63 theorems of `Safety.lean` are proved; the 34 theorems of `Liveness.lean` have proof `sorry`, except the four that read no game definition. The statements are the deliverable.

Source order (`armada-laconic/docs/lean/writing-lean.md`, "Source order"): the primary source of every declaration is the latest paper that covers it, SATP (2022), then Nitro (2019), then ForceMove (2018). Each definition was then checked against go-nitro at `64c4ee9a1` (`packages/nitro-protocol/contracts/`, last contract change `9d3a669e5`), fetched by a shallow clone under `.scratch/go-nitro`. Where the code corrects a paper, the code is followed and both are cited. Where the code differs only by encoding, the paper form is kept and the difference is noted.

## Modules

| Module | Content | Primary source |
|---|---|---|
| `ArmadaLean/Nitro/Address.lean` | coins, time, participants, fixed part, destinations (`Address E`: a channel or an external destination of the parameter type `E`), balances | SATP §2.1, §2.4; Nitro §3.1 for balances; go-nitro INitroTypes.sol, MultiAssetHolder.sol |
| `ArmadaLean/Nitro/Outcome.lean` | items, allocations, priority payout, afford, outcomes | SATP §2.4; go-nitro MultiAssetHolder.sol; Nitro §5.1 for afford |
| `ArmadaLean/Nitro/Channel.lean` | states, signed states, application rules, ForceMove and consensus rules, channel status and modes | SATP §2.1-2.3; go-nitro ForceMove.sol, StatusManager.sol, Consensus.sol |
| `ArmadaLean/Nitro/Adjudicator.lean` | the adjudicator state and the operations deposit, transfer, reclaim, challenge, checkpoint, conclude, tick; `Step`, `Reachable` | go-nitro ForceMove.sol, MultiAssetHolder.sol; SATP Listings 1-2; Nitro §3.1, §5.1 |
| `ArmadaLean/Nitro/Strategy.lean` | network states, moves, threat model (`Threat.ε`, `Threat.Round`), `Bounds`, `Capable`, `Assumptions`, `UnbeatableIn`, `Unbeatable`, `Run`, `Prevents`, finalizable, enabled, funded, value | Nitro §4 (SATP and go-nitro have no off-chain model); SATP:164-168 and Nitro:537-542 for the assumptions |
| `ArmadaLean/Nitro/Value.lean` | outcome network, DAG, Turbo Value Algorithm | Nitro §5.2 |
| `ArmadaLean/Nitro/Constructions.lean` | ledger channels with sub-channels | Nitro §5.3-5.4; the virtual channel is in SATP.lean |
| `ArmadaLean/Nitro/SATP.lean` | vouchers, the virtual channel rules, routes, Protocols 3.1-3.3 state | SATP §3, Appendix A |
| `ArmadaLean/Nitro/Lemmas.lean` | the `@[simp]` reading lemmas of balances, allocations, payouts, channel statuses and the operations; the coins-held invariant `Adjudicator.HeldInv` | no source: proof helpers for `Safety.lean` |
| `ArmadaLean/Nitro/Safety.lean` | 63 theorems, all proved: on-chain safety, conservation, data operations | go-nitro and SATP first |
| `ArmadaLean/Nitro/Liveness.lean` | 34 theorems: unbeatable strategies, the Turbo value algorithm, ledger constructions, SATP Lemma 3.1 and Theorem 3.2 | SATP §3; Nitro §4-5 |
| `ArmadaLean/Nitro/NonVacuity.lean` | one proved witness per theorem with hypotheses (verification.md §5a): 54 for `Safety.lean`, 34 for `Liveness.lean`; the strategies "conclude now" and "wait until the deadline" | no source: acceptance check |

## Paper vs code: where go-nitro is followed over the latest paper

- **Challenge rule.** SATP Listing 1 (SATP:303-305) accepts a challenge whenever `isOpen` and `version >= recorded`, so a re-challenge at an equal version during a running challenge resets the deadline. go-nitro ForceMove.sol:46-54 requires a non-decreased turn in Open mode, a strictly higher turn in Challenge mode, and reverts in Finalized mode. The model follows the code (`Adjudicator.challenge`; theorems `challenge_requires`, `rechallenge_equal_turn_fails`, `challenge_fails_when_finalized`). ForceMove:1341-1342 forbade any challenge during a challenge; the code allows one at a higher turn.
- **Checkpoint replaces respond.** go-nitro has `checkpoint` (ForceMove.sol:85-114): not finalized, strictly higher turn, supported; it sets Open and clears a challenge. It has no `respond` operation. SATP has neither. ForceMove `refute`/`respondWithMove`/`alternativeRespondWithMove` are superseded. The earlier `respond` is removed; `Adjudicator.checkpoint` is the operation.
- **Conclude needs unanimous signatures and does not call the app.** SATP:286-289 says a final state is "supported" and submitted; go-nitro `_conclude` (ForceMove.sol:136-164) requires `isFinal` and `getClaimedSignersNum(signedBy) == participants.length` and never calls `stateIsSupported`. The model follows the code: `Adjudicator.conclude` takes one signed state and requires `ConclusionProof` (theorem `conclude_needs_all`).
- **No withdrawal operation.** Nitro:169-199 defines `W_A(x)`; SATP:764-768 defers withdrawals. go-nitro has no withdraw: `_executeSingleAssetExit` (MultiAssetHolder.sol:402-415) pays an external destination straight out of the contract during `transfer`. The model follows the code: `Adjudicator.payTo` lowers `held` when the destination is external; an external balance is the coins paid out to it (theorems `held_falls_only_by_payout`, `paid_out_monotone`, `held_eq_channel_balances`).
- **Deposit only to a channel.** Nitro:227-228: "Anyone can deposit into an address of either type". go-nitro MultiAssetHolder.sol:43 reverts on an external destination. The model follows the code (`Adjudicator.deposit` returns `none` for an external destination; theorem `deposit_to_external_fails`).
- **Transfer pays the whole affordable amount.** Nitro:765-772 `T(A, B, x)` takes an amount `x` up to the affordable amount. go-nitro `transfer` (MultiAssetHolder.sol:66, 162-191) pays "as many funds ... as can be afforded" for the selected entry, and reverts on a guarantee entry (line 172). The model follows the code: `Adjudicator.transfer a b` has no amount parameter (theorems `transfer_effects`, `transfer_fails_otherwise`).
- **Reclaim checks.** SATP Listing 2 (SATP:358-361) does `o_ledger[left] += o_target[0]`, `o_ledger[right] += o_target[1]`, `delete`. go-nitro `compute_reclaim_effects` (MultiAssetHolder.sol:363-365) also requires that `left` and `right` have entries in the ledger and that `o_target[0] + o_target[1]` equals the guarantee amount. The model follows the code (`Adjudicator.reclaim`; theorems `reclaim_requires`, `reclaim_fails_without_entries`). This removes the earlier "append on a missing key" choice.
- **Challenger must be a participant.** SATP Listing 1 has no caller check. go-nitro `_requireChallengerIsParticipant` (ForceMove.sol:178-190) requires it; ForceMove:1545-1548 proposed it. The model follows the code.
- **Channel id includes challengeDuration.** SATP:213 hashes `(peers, appDef, nonce)`; go-nitro NitroUtils.sol:122-133 hashes the four fixed fields. The model id is the whole fixed part, as in the code.

## Histories, reorganizations and expectedHeld (operator ruling 2026-10-27)

The model has no forks and no finality: the papers make no confirmation claims. A reorganization is not an operation; a history that drops or reorders earlier deposits is just another `Reachable` history, and every theorem over all histories covers it. go-nitro `deposit` (MultiAssetHolder.sol:38-63) takes `expectedHeld`, the holding the depositor saw, and fails unless the chain still holds it (lines 45-49 give the reorg scenario). `Adjudicator.deposit` is that compare-and-swap guard. The funding-order theorem `deposit_respects_funding_order` and the can-happen theorem `deposits_in_order_succeed` state ForceMove §6.2 (ForceMove:1197-1208, 1797-1808) over every history. The earlier note that `expectedHeld` was unmodelled is withdrawn; the forbidden-encoding check now allows the word.

## Mathlib (operator ruling 2026-10-27)

Mathlib `v4.33.1` is a dependency. Hand-written definitions replaced by Mathlib ones, with the meaning unchanged: `Reachable` is `Relation.ReflTransGen (Step apps) genesis`; `Redistributed` is `Relation.ReflTransGen RedistributeStep` (the one-step inductive stays); `Acyclic edge` is `Std.Irrefl (Relation.TransGen edge)`, whose `irrefl` field is the ruling's `∀ c, ¬ TransGen edge c c`. Sums stay core `List.sum`; `List.lookup`, `List.Nodup`, `List.all` are core.

## Operator ruling 2026-10-27: reclaim only

The specification keeps only `reclaim` (SATP Listing 2, go-nitro `MultiAssetHolder.reclaim`). Nitro 2019's `claim`, the guarantee-channel outcome, the reprioritization rule, the Minimum Payout Calculation, the Nitro Lower-bound Value Algorithm and the Nitro §6.3-6.5 guarantee-channel construction are dropped. The affected ids (Nitro-39 to Nitro-48, and the §6.5 part of Nitro-49) are `superseded-by SATP-15`. Removed theorems: `claim_requires`, `claim_effects`, `claim_fails_otherwise`, `reprioritize_example`, `reprioritize_keeps_amounts`, `claim_order_dependent`, `nitro_lower_bound_achievable`, `nitro_lower_bound_underestimates`, `overfunded_min_payout`, `fully_funded_min_payout`, `single_guarantee_determined`, `figure23_lower_bound`, `end_participant_offloads`, `intermediary_recovers_collateral`, `virtual_open_value_preserving`, `virtual_close_value_preserving`. Every guarantee-item theorem that `reclaim` uses is kept.

## Operator ruling 2026-10-27: channel types by construction

SATP §1 (SATP:79-84): "ledger channels, which are typically funded by the
underlying ledger, and virtual channels, which are funded by ledger
channels." A ledger channel is funded by deposits or by an allocation in
another channel's outcome. A virtual channel is funded only by guarantees
held in two or more ledger channels and holds no assets of its own.
`FixedPart` carries a field `kind : ChannelKind` (`ledger` or `virtual`,
`Address.lean`) fixed at construction, never changed after the channel
opens (the on-chain channel id is an untyped hash of the fixed part, so the
type is an addition to the specification, not an encoding of the chain).
`Adjudicator.deposit` and `Adjudicator.transfer` succeed only for a ledger
channel (`transfer`'s paid destination too, when it names a channel); a
guarantee names only a virtual channel as its `reclaim` target.
`Adjudicator.reclaim` reads the target's outcome of finalization
(`finalizedWith`, SATP §2.4 SATP:335-338), not its current stored outcome:
this is the fix for the reclaim denial-of-service reproduced against
go-nitro at `64c4ee9a1`
(`armada-laconic/labbook/2026-10-27-gonitro-reclaim-dos.md`), where a
griefer deposits into a finalized virtual channel, pays itself out by
`transfer`, and every later `reclaim` reverts forever. `Route.WellFormed`
(`SATP.lean`) requires `kind = .ledger` for each ledger and `.virtual` for `V`;
`satp_reclaim_credits_intermediary` carries the matching hypotheses and
stays proved. Every theorem whose type changed, with its old and new text,
is `docs/nitro-repair-2026-10-27.md` §6. Operator ruling 2026-10-27:
`transfer_pays_at_most_held`, `reclaim_moves_guarantee_amount` and
`virtual_finalized_outcome_immutable`, proposed for this ruling, are
removed as not paper theorems; `docs/nitro-repair-2026-10-27.md` §6.3.

## Encoding differences noted, paper form kept

- go-nitro stores a hash of the state and outcome and packs `turnNumRecord`, the finalization time and a fingerprint into one slot (StatusManager.sol); the model stores values (`ChannelStatus`).
- go-nitro marks "no challenge" by a zero finalization time (StatusManager.sol:8); the model has explicit constructors `open`, `challenged`, `finalized`.
- go-nitro resets the stored turn to 0 on conclude (ForceMove.sol:157); no operation reads the turn of a finalized channel, so the model keeps the candidate turn. A conclude can lower the stored turn (see "Corrections after approval"); `turnNumRecord_monotone` states that exception.
- go-nitro `transfer` takes an `indices` batch and `transferAllAssets`/`concludeAndTransferAllAssets` batch several calls; the model has single-destination operations.
- go-nitro represents signers as a bitmask (INitroTypes.sol:34); the model uses a signer list.
- go-nitro is multi-asset (`holdings[asset][channelId]`); the model is one single-asset instance.
- go-nitro Consensus.sol takes an empty proof and a unanimous candidate; SATP:262-266 takes one unanimous state in `vars`. The model keeps SATP's shape (`consensusRules`): the one proof state is the candidate.
- go-nitro `transfer` "Assumes no repeated entries" (MultiAssetHolder.sol:67); Nitro:744-746 ignores repeats after the first. The model keeps the paper rule (`Allocation.dedup`).
- go-nitro VirtualPaymentApp.sol is the unidirectional special case (SATP:444-449) of SATP Appendix A; the model keeps the two-way rules of SATP Listing 3, which Lemma 3.1 and Theorem 3.2 rest on.

## Modelling choices the papers and the code do not force

- Single asset: one instance; a multi-asset adjudicator is a family of independent instances, because no operation in SATP, Nitro or go-nitro moves value between assets. Approved by the operator, 2026-10-27.
- Symbolic hash and signatures: a channel address is the constructor `Address.channel` applied to the fixed part, so injectivity holds by construction; a signed state carries its signer list; forgery is the game rule `Assumptions.unforgeable`, a named hypothesis. Approved by the operator, 2026-10-27.
- Applications: `Apps := AppId → Rules`; `Rules.supports` is a computable `Bool` function, as go-nitro `stateIsSupported` returns `bool`. Operator ruling 2026-10-27 (this replaced a `Prop` with classical decisions; `challenge`, `checkpoint` and `conclude` are computable and `#eval` runs them). The ForceMove game library `vt` and the SATP `validateOutcomeChange` are `Bool` functions too.
- The game (Nitro §4): one adversary controls every other participant (Nitro:460-461). One round of `Unbeatable` is: the honest participant chooses one move, the adversary plays a finite feasible prefix, then the move is applied; this is front-running (Nitro:540-542). The clock follows Nitro:537-539: "given that the current time is t and ε > 0, then it is possible for any party to apply any operation, O, on-chain before time t + ε". The adversary may move the clock, but each honest move lands before `ε` has passed since it was chosen (`Threat.Round`); the liveness theorems assume challenge durations of at least `2 * ε` (a challenge registered just after `p` chose a move is answered by the next move). The honest participant does not deposit (Nitro:779-781; `p` has no wallet). `Unbeatable` is `UnbeatableIn` with every move allowed, an inductive strategy tree; `Prevents` asks for a total, feasible strategy whose every play of rounds avoids the goal. `Finalized` reads the outcome of finalization, which a payout does not change. Repair of 2026-10-27: `docs/nitro-repair-2026-10-27.md`; it replaces the rule "only the honest `wait` reaches a deadline" approved on 2026-10-27.
- DAG: operator ruling 2026-10-27. "The network of outcomes is a DAG" means no channel reaches itself by following edges: `Acyclic edge := ∀ c, ¬ Relation.TransGen edge c c` with `edge A B` = "A's outcome allocates to channel B" (`Adjudicator.Edge`, `Adjudicator.IsDAG`). No theorem type carries a topological ordering; the Turbo Value Algorithm's result is the relation `Adjudicator.TurboValue n x` (some topological ordering gives `x`), and `turbo_value_exists_unique` states that on a DAG it exists and is unique. A proof that needs an ordering derives it as a lemma (Nitro:798-799).
- SATP app data: operator ruling 2026-10-27 (choice 5, changed). The state carries the parsed value: `State.appData : AppData` with constructors `satpVirtual (d : VirtualAppData)` and `opaque label`. The earlier `Decode : Nat → VirtualAppData` parameter and every `decode` argument are removed. ABI encoding, decoding and the round-trip theorem `decode (encode v) = some v` belong to the refinement layer, not to this branch.
- The theorems of `Liveness.lean` have proof `sorry`, except the four that read no game definition (`ledger_topup_reorder_safe`, `ledger_topup_deposit_funds`, `satp_outcome_change_keeps_total`, `satp_reclaim_credits_intermediary`). The theorems of `Safety.lean` are proved (branch `nitro-proofs`).

## Corrections after approval (operator ruling 2026-10-27)

Six approved `Safety.lean` statements were false. A Lean proof of each negation type-checked against the approved statements at `nitro-theorems-approved-2026-10-27` (`69b9ea2`), with axioms `[propext]` only. The file was a scratch file outside the build. The operator approved the corrections below on 2026-10-27. No other statement changed.

Counterexample A. The state is unreachable. The channel `c` holds 10 and the contract holds 5 (`held = 5`). The outcome of `c` is finalized as `[participant p : 10]`. `transfer c p` pays `x = 10`, and `held` becomes `5 - 10 = 0` in `Nat`.

- `held_falls_only_by_payout`. The coins held fall by 5, but `p` receives 10. Correction: add `(hr : Reachable apps s)`.
- `transfer_effects`. The last conjunct reads `0 + 10 = 5`. Correction: add `(apps : Apps)` and `(hr : Reachable apps s)`.
- `redistribution_conserves_total`. `s'.held + paidOut' = 0 + 10`, but `s.held + paidOut = 5 + 0`. Correction: add `(hr : Reachable apps s)`. On an unreachable state an address can also have two balance entries; `Balances.set` drops both.

With `Reachable`, the invariant `Adjudicator.HeldInv` (one balance entry per address, and `held = channelTotal`) gives `x ≤ held`.

Counterexample B. The state is reachable: a conclude of `c` with outcome `[participant p : 5]` and no deposit. `transfer c p` pays 0. The balance list changes from `[]` to `[(c, 0), (p, 0)]`, because `Balances.add b 0` writes an entry.

- `transfer_zero_moves_nothing`. The list equality `s'.balances = s.balances` is false. Correction: `∀ d, s'.balances.get d = s.balances.get d`.

Counterexample C. The state is reachable: a checkpoint of `c` at turn 5, then a conclude of `c` with a final state at turn 0. `Adjudicator.conclude` has no turn check and stores the candidate's turn, so the stored turn falls from 5 to 0.

- `turnNumRecord_monotone`. Correction: the stored turn does not fall, or the step is a conclude of `c` and `c` is finalized after it.

Counterexample D, two cases. Both states are reachable by conclude steps.

- `reclaim_effects`, case `l = v`. The ledger `c` has outcome `[p : 1, q : 1, c : G(2, [p, q])]` and reclaims itself. After the reclaim, `s'.finalOutcome v` is the new ledger outcome `[p : 2, q : 2]`, so the last conjunct is false. Correction: add `(hne : l ≠ v)`. The name `hlv` was already in use for `left ≠ v.address`.
- `reclaim_effects`, a second entry for `v`. The ledger outcome is `[v : G(2, [p, q]), v : 3, p : 0, q : 0]` and the target outcome is `[p : 1, q : 1]`. `Allocation.remove` deletes both entries for `v`, so the total falls from 5 to 2. Correction: add `(hdedup : oL.dedup = oL)` (Nitro-25: each address appears once in an allocation).

## Property map (189 ids)

The ids keep the numbering of the extraction reports. The report label is replaced by the source name:

| Report prefix | Source name | Source |
|---|---|---|
| S1 | ForceMove | Close and Stewart, ForceMove, 2018 |
| S2 | Nitro | Close, Nitro Protocol, ePrint 2019/219 |
| S3 | SATP | Stewart et al., SATP, 2022 |
| S4 | docs | docs.statechannels.org tutorial |

Disposition forms: `theorem NAME`, `definition NAME`, `assumption field NAME`, `superseded-by ID`, `out of scope: reason`.

| Id | Disposition |
|---|---|
| ForceMove-D01 | definition FixedPart, FixedPart.address |
| ForceMove-D02 | theorem channel_address_inj, channel_address_ne_external |
| ForceMove-D03 | definition Outcome, Allocation |
| ForceMove-D04 | definition SignedState |
| ForceMove-D05 | definition State, State.mover |
| ForceMove-D06 | theorem mover_determined_by_turn, mover_cyclic |
| ForceMove-D07 | definition State (field appData) |
| ForceMove-D08 | definition State (field isFinal, the SATP form of the conclude state type) |
| ForceMove-D09 | superseded-by Nitro-23 (definition AtFundingPoint) |
| ForceMove-D10 | superseded-by Nitro-23 (definition AtFundingPoint) |
| ForceMove-D11 | definition Mode, ChannelStatus.mode |
| ForceMove-D12 | definition Challenge, ChannelStatus.mode; theorem challenge_in_progress_before_deadline, timeout_finalizes |
| ForceMove-D13 | definition Op |
| ForceMove-A01 | theorem forceMove_supports_valid_run |
| ForceMove-A02 | theorem forceMove_supports_valid_run (definition UniversalTransition) |
| ForceMove-A03 | definition ValidMove, ConclusionTransition (the per-type dispatch folds into one predicate) |
| ForceMove-A04 | theorem forceMove_conclude_keeps_outcome, conclude_moves_no_value |
| ForceMove-A05 | theorem forceMove_conclude_keeps_outcome |
| ForceMove-A06 | superseded-by Nitro-23 (hypothesis SetupPhaseKeepsOutcome in funding_point_universally_finalizable) |
| ForceMove-A07 | superseded-by Nitro-23 (hypothesis SetupPhaseKeepsOutcome in funding_point_universally_finalizable) |
| ForceMove-A08 | theorem forceMove_conclude_keeps_outcome |
| ForceMove-A09 | theorem conclude_needs_all (definition ConclusionProof, the SATP and go-nitro form) |
| ForceMove-A10 | theorem challenge_requires, challenge_can_happen, challenge_fails_when_finalized (go-nitro allows a challenge during a challenge at a higher turn) |
| ForceMove-A11 | theorem checkpoint_requires, checkpoint_can_happen (go-nitro checkpoint replaces refute) |
| ForceMove-A12 | theorem checkpoint_requires, checkpoint_can_happen (go-nitro checkpoint replaces respondWithMove) |
| ForceMove-A13 | superseded-by ForceMove-A12 (go-nitro has no alternative moves; one supported candidate is checkpointed) |
| ForceMove-A14 | theorem conclude_can_happen, finalized_permanent |
| ForceMove-A15 | theorem transfer_requires_finalized |
| ForceMove-A16 | theorem payout_priority_formula |
| ForceMove-A17 | superseded-by Nitro-02 (definition Adjudicator.statusOf: one contract, many channels) |
| ForceMove-A18 | theorem checkpoint_can_happen |
| ForceMove-A19 | definition Rules (pure by construction: the rules read only states) |
| ForceMove-A20 | theorem failed_op_no_effect |
| ForceMove-A21 | theorem turnNumRecord_monotone, challenge_requires |
| ForceMove-B01 | theorem directly_funded_pays, latest_state_finalizable |
| ForceMove-B02 | theorem checkpoint_requires, turnNumRecord_monotone |
| ForceMove-B03 | theorem timeout_finalizes |
| ForceMove-B04 | theorem checkpoint_can_happen |
| ForceMove-B05 | theorem late_observer_can_checkpoint |
| ForceMove-B06 | theorem funding_point_universally_finalizable |
| ForceMove-B07 | theorem payout_earlier_paid_in_full, deposit_respects_funding_order |
| ForceMove-C01 | theorem deposit_can_happen, deposits_in_order_succeed |
| ForceMove-C02 | theorem challenge_can_happen |
| ForceMove-C03 | theorem transfer_can_happen |
| ForceMove-E01 | out of scope: app-specific game logic (ForceMove:536-551 Specification 1 is a payment-game library rule, not an adjudicator rule) |
| ForceMove-E02 | out of scope: app design incentive (ForceMove:339-346 commit-reveal default winner is a game-library choice) |
| ForceMove-E03 | superseded-by ForceMove-A12 (alternative moves are dropped; ForceMove:781-797) |
| ForceMove-E04 | out of scope: participant behaviour (ForceMove:1187-1196 rational backing out is a choice, not a guarantee) |
| ForceMove-E05 | out of scope: economic limit (ForceMove:1566-1586: griefing cannot be eliminated; the deposit extension is optional and not a claim of the protocol) |
| ForceMove-F01 | definition Address (the hash is a constructor; theorem channel_address_inj) |
| ForceMove-F02 | assumption field Assumptions.unforgeable |
| ForceMove-F03 | definition Adjudicator.tick, Challenge (field deadline) |
| ForceMove-F04 | theorem held_eq_channel_balances |
| ForceMove-F05 | theorem funding_decoupled_from_rules |
| Nitro-01 | theorem balances_absent_zero (definition Balances.get) |
| Nitro-02 | definition FixedPart.address; theorem channel_address_inj |
| Nitro-03 | assumption field Assumptions.unforgeable (the channel-address half holds by construction of Address) |
| Nitro-04 | theorem deposit_can_happen, deposit_to_external_fails (go-nitro: only a channel address; Nitro:227-228 allowed either) |
| Nitro-05 | theorem deposit_effects, held_eq_channel_balances |
| Nitro-06 | theorem held_falls_only_by_payout, paid_out_monotone (go-nitro has no withdraw; a transfer pays the external destination directly) |
| Nitro-07 | theorem channel_balance_falls_only_by_redistribution |
| Nitro-08 | theorem held_eq_channel_balances, balances_total_split, redistribution_conserves_total, held_changes_only_by_deposit_payout |
| Nitro-09 | definition Allocation, Entry |
| Nitro-10 | theorem transfer_requires_finalized |
| Nitro-11 | theorem finalized_two_ways |
| Nitro-12 | theorem challenge_can_happen, timeout_finalizes, latest_state_finalizable |
| Nitro-13 | theorem conclude_can_happen, conclude_needs_all, conclusion_proof_finalizable |
| Nitro-14 | theorem finalized_permanent, finalized_outcome_only_redistributed |
| Nitro-15 | theorem redistribution_ignores_caller |
| Nitro-16 | theorem directly_funded_pays |
| Nitro-17 | definition FundedFor, Adjudicator.DirectlyFunded |
| Nitro-18 | definition Value; theorem turbo_value_is_value |
| Nitro-19 | game rule Threat.ε, Threat.Round (Nitro:537-539) |
| Nitro-20 | definition Unbeatable (front-running is the adversary prefix in Unbeatable.move) |
| Nitro-21 | definition Finalizable; theorem finalizable_funded_pays, finalizable_or_two_enabled, single_enabled_is_finalizable |
| Nitro-22 | theorem finalizable_unique, channel_finalizability_cases |
| Nitro-23 | theorem funding_point_universally_finalizable, concluded_universally_finalizable |
| Nitro-24 | definition Enabled; theorem finalizable_or_two_enabled, single_enabled_is_finalizable |
| Nitro-25 | definition Allocation.dedup; theorem paidTo_first_entry_only |
| Nitro-26 | theorem payout_priority_formula, payout_bounded |
| Nitro-27 | definition Allocation.Affords; theorem affords_when_fully_funded |
| Nitro-28 | theorem transfer_effects, reduceOwed_owed, transfer_can_happen (go-nitro pays the whole affordable amount; x is not a parameter) |
| Nitro-29 | theorem transfer_fails_otherwise, transfer_zero_moves_nothing |
| Nitro-30 | theorem turbo_redistribution_unbeatable |
| Nitro-31 | theorem deposit_bounds_value, payout_to_other_affects_only_owner (definitions Threat.TransfersOnly, Threat.CapableTransfers, HonestMove.IsTransfer) |
| Nitro-32 | definition Acyclic, Adjudicator.IsDAG; theorem participant_can_prevent_cycles, turbo_value_exists_unique |
| Nitro-33 | definition Adjudicator.TurboValue, Adjudicator.turboValueAlong |
| Nitro-34 | theorem turbo_value_upper_bound |
| Nitro-35 | theorem turbo_value_achievable |
| Nitro-36 | theorem turbo_order_independent, turbo_value_exists_unique |
| Nitro-37 | theorem ledger_offload_funds_subchannel |
| Nitro-38 | definition Outcome, Op (allocation and reclaim only; the guarantee outcome and claim are superseded-by SATP-15, ruling 2026-10-27) |
| Nitro-39 | superseded-by SATP-15 (reclaim; operator ruling 2026-10-27: Nitro 2019 claim and the guarantee channel are dropped) |
| Nitro-40 | superseded-by SATP-15 (reclaim; operator ruling 2026-10-27: Nitro 2019 claim and the guarantee channel are dropped); the reclaim form is theorem reclaim_requires |
| Nitro-41 | superseded-by SATP-15 (reclaim; operator ruling 2026-10-27: Nitro 2019 claim and the guarantee channel are dropped) |
| Nitro-42 | superseded-by SATP-15 (reclaim; operator ruling 2026-10-27: Nitro 2019 claim and the guarantee channel are dropped) |
| Nitro-43 | superseded-by SATP-15 (reclaim; operator ruling 2026-10-27: Nitro 2019 claim and the guarantee channel are dropped); the reclaim form is theorem reclaim_effects |
| Nitro-44 | superseded-by SATP-15 (reclaim; operator ruling 2026-10-27: Nitro 2019 claim and the guarantee channel are dropped) |
| Nitro-45 | superseded-by SATP-15 (reclaim; operator ruling 2026-10-27: Nitro 2019 claim and the guarantee channel are dropped) |
| Nitro-46 | superseded-by SATP-15 (reclaim; operator ruling 2026-10-27: Nitro 2019 claim and the guarantee channel are dropped) |
| Nitro-47 | superseded-by SATP-15 (reclaim; operator ruling 2026-10-27: Nitro 2019 claim and the guarantee channel are dropped); the ledger offload is theorem ledger_offload_funds_subchannel |
| Nitro-48 | superseded-by SATP-15 (reclaim; operator ruling 2026-10-27: Nitro 2019 claim and the guarantee channel are dropped); the SATP form of intermediary recovery is theorem satp_theorem_3_2 |
| Nitro-49 | theorem consensus_enabled_outcomes, subchannel_open_value_preserving, subchannel_close_value_preserving, ledger_topup_reorder_safe, ledger_topup_deposit_funds, ledger_partial_withdrawal (the §6.5 virtual channel sequences are superseded-by SATP-15 Protocols 3.1-3.2, ruling 2026-10-27) |
| SATP-01 | definition FixedPart |
| SATP-02 | definition State, AppData |
| SATP-03 | definition State (FixedPart plus the variable fields) |
| SATP-04 | definition ChannelStatus, Adjudicator.statusOf |
| SATP-05 | definition FixedPart.address; theorem channel_address_inj |
| SATP-06 | definition SupportProof |
| SATP-07 | definition Rules |
| SATP-08 | definition consensusRules (go-nitro Consensus.sol agrees) |
| SATP-09 | definition Item (constructor alloc) |
| SATP-10 | definition Item (constructor guarantee) |
| SATP-11 | definition Item.amount |
| SATP-12 | definition Allocation; theorem payout_priority_formula |
| SATP-13 | definition ChannelStatus.IsOpen; theorem isOpen_iff |
| SATP-14 | theorem challenge_requires, challenge_can_happen, rechallenge_equal_turn_fails, challenge_fails_when_finalized (go-nitro: strict turn in Challenge mode; SATP Listing 1 would allow an equal version) |
| SATP-15 | theorem reclaim_requires, reclaim_effects, reclaim_can_happen, reclaim_fails_without_entries (go-nitro adds the left/right and amount checks) |
| SATP-16 | theorem finalized_two_ways, conclude_can_happen, held_falls_only_by_payout |
| SATP-17 | definition satpVirtualRules |
| SATP-18 | definition validateOutcomeChange, validStart, validChallenge, validResponse, VirtualAppData, Voucher, VType (Bool on the structured app data, ruling 2026-10-27) |
| SATP-19 | theorem satp_outcome_change_keeps_total |
| SATP-20 | theorem satp_theorem_3_2, satp_intermediary_before_round2, satp_end_user_recovers, satp_reclaim_credits_intermediary |
| SATP-21 | theorem satp_lemma_3_1, satp_peers_can_finalize |
| SATP-22 | out of scope: gas cost and wall-clock bound (SATP:491-493 Theorem 3.1); the model has no cost or duration measure |
| SATP-23 | out of scope: conjecture (SATP:451-452 Conjecture 3.1 is stated, not claimed proved) |
| SATP-24 | game rule Threat.ε, Threat.Round (Nitro:537-539) |
| SATP-25 | assumption field Assumptions.unforgeable |
| SATP-26 | superseded-by Nitro-04 (SATP:764-768 defers deposits and withdrawals; the model takes deposit from go-nitro and Nitro §3.1, and go-nitro has no withdrawal) |
| docs-0010-01 | definition FixedPart, State |
| docs-0010-02 | theorem channel_address_inj |
| docs-0010-03 | out of scope: docs-only contract encoding (stateHash, go-nitro NitroUtils.sol); the model stores values, not hashes |
| docs-0010-04 | out of scope: docs-only contract encoding (signedBy bitmask, go-nitro INitroTypes.sol:34); definition SignedState carries the signer list |
| docs-0030-01 | out of scope: docs-only multi-asset exit encoding; the model is one single-asset instance (Nitro:142-148) |
| docs-0030-02 | out of scope: docs-only allocationType and metadata encoding; definition Item carries the two kinds |
| docs-0030-03 | theorem transfer_effects (Nitro-28 supports it) |
| docs-0030-04 | theorem reclaim_requires, transfer_fails_otherwise (SATP-15 and go-nitro support it; a guarantee entry cannot be transferred) |
| docs-0030-05 | out of scope: docs-only 32-byte destination encoding; definition Address has the two kinds |
| docs-0040-01 | definition Mode |
| docs-0040-02 | definition ChannelStatus.mode (SATP-13 and go-nitro StatusManager.sol support it; the zero sentinel is an encoding) |
| docs-0040-03 | out of scope: reset of the stored turn to 0 on conclude (go-nitro ForceMove.sol:157); no operation reads the turn of a finalized channel, so it is an encoding (the monotone half is theorem turnNumRecord_monotone) |
| docs-0040-04 | out of scope: docs-only storage packing (go-nitro StatusManager.sol); the model stores the status as a value |
| docs-0040-05 | theorem timeout_finalizes, tick_moves_only_time |
| docs-0020-01 | definition consensusRules |
| docs-0010-05 | theorem conclude_can_happen |
| docs-0060-01 | theorem deposit_to_external_fails (go-nitro MultiAssetHolder.sol:43 is followed over Nitro:227-228) |
| docs-0060-02 | theorem deposit_requires_expectedHeld, deposit_respects_funding_order, deposits_in_order_succeed, deposit_effects (definition Adjudicator.deposit, Allocation.aheadOf; operator ruling 2026-10-27) |
| docs-0060-03 | theorem deposit_effects |
| docs-0070-01 | theorem conclude_needs_all |
| docs-0070-02 | theorem challenge_requires |
| docs-0070-03 | theorem turnNumRecord_monotone, challenge_requires, checkpoint_requires |
| docs-0070-04 | theorem finalized_two_ways |
| docs-0080-01 | theorem transfer_requires_finalized, reclaim_requires |
| docs-0080-02 | out of scope: docs-only stored-hash matching (go-nitro _requireMatchingFingerprint); the model stores the outcome value |
| docs-0080-03 | theorem payout_bounded, transfer_effects |
| docs-0070-05 | theorem conclusion_proof_finalizable, directly_funded_pays |
| docs-0070-06 | theorem latest_state_finalizable |
| docs-C-01 | theorem held_eq_channel_balances |
| docs-C-02 | out of scope: Armada note-pool encoding; not in the papers or go-nitro |
| docs-0070-07 | theorem conclude_moves_no_value |
| docs-0080-04 | theorem transfer_effects (the transfer pays exactly x) |
| docs-0060-04 | theorem deposit_can_happen |
| docs-0060-05 | theorem deposit_effects, ledger_topup_deposit_funds |
| docs-0070-08 | theorem challenge_can_happen |
| docs-0040-06 | theorem timeout_finalizes |
| docs-0070-09 | theorem conclude_can_happen |
| docs-0080-06 | theorem transfer_can_happen |
| docs-0080-05 | theorem reclaim_can_happen, reclaim_effects |
| docs-0070-10 | theorem checkpoint_can_happen, checkpoint_requires |
| docs-0010-06 | out of scope: docs-only client check on the participant list |
| docs-0010-07 | theorem channel_address_inj (ForceMove-D02 supports it) |
| docs-0010-08 | out of scope: docs-only parameter bound; the theorems take 0 < challengeDuration as a hypothesis |
| docs-0010-09 | out of scope: docs-only overflow bound; Nitro:144 takes quantities with no maximum |
| docs-0010-10 | out of scope: docs-only client behaviour (stop executing after isFinal) |
| docs-0020-02 | definition Rules |
| docs-0020-03 | definition satpVirtualRules (SATP Appendix A; go-nitro VirtualPaymentApp.sol is the unidirectional special case) |
| docs-0040-07 | out of scope: docs-only client lifecycle states; the on-chain modes are definition Mode |
| docs-0040-08 | superseded-by Nitro-17 (definition FundedFor) |
| docs-0040-09 | out of scope: docs-only client behaviour (when to fund and defund) |
| docs-0040-10 | superseded-by Nitro-23 (theorem funding_point_universally_finalizable) |
| docs-0060-06 | theorem payout_earlier_paid_in_full, deposit_respects_funding_order (ForceMove-B07 supports it) |
| docs-0060-07 | theorem ledger_offload_funds_subchannel, subchannel_open_value_preserving |
| docs-0060-08 | theorem satp_theorem_3_2, satp_reclaim_credits_intermediary (SATP Protocol 3.1) |
| docs-0060-09 | out of scope: docs-only ETH/ERC20 chain mechanics (go-nitro MultiAssetHolder.sol:53-57) |
| docs-0070-11 | theorem checkpoint_can_happen (go-nitro has checkpoint, no respond; the event-caching half is docs-only client infrastructure) |
| docs-0070-12 | out of scope: docs-only client infrastructure; the model stores values, not hashes |
| docs-0080-07 | theorem subchannel_close_value_preserving, satp_reclaim_credits_intermediary |
| docs-0080-08 | theorem ledger_offload_funds_subchannel, reclaim_can_happen |
| docs-0080-09 | out of scope: docs-only client tracking of events |

### Counts per disposition

- assumption: 5
- definition: 46
- out of scope: 24
- superseded-by: 20
- theorem: 94
- total: 189

## Theorems (97)

| Theorem | Module | Meaning | Property ids | Source |
|---|---|---|---|---|
| `channel_address_inj` | `Safety.lean` | One address names one channel. | ForceMove-D02, ForceMove-F01, Nitro-02, Nitro-03, SATP-05, docs-0010-02 | SATP:213-215 |
| `channel_address_ne_external` | `Safety.lean` | A channel address is never an external destination. | ForceMove-D02, Nitro-02 | docs |
| `balances_absent_zero` | `Safety.lean` | An absent address has balance zero. | Nitro-01 | Nitro:162-163 |
| `held_eq_channel_balances` | `Safety.lean` | Coins held equal the sum of channel balances on every reachable state. | ForceMove-F04, Nitro-05, Nitro-08, docs-C-01 | Nitro:230-231 |
| `balances_total_split` | `Safety.lean` | All balances = channel balances + coins paid out. | Nitro-08 | docs |
| `deposit_effects` | `Safety.lean` | A successful deposit saw expectedHeld and adds exactly x to that holding and to the coins held. | ForceMove-C01, Nitro-04, Nitro-05, docs-0060-02, docs-0060-03, docs-0060-04, docs-0060-05 | go-nitro MultiAssetHolder.sol:51 |
| `deposit_can_happen` | `Safety.lean` | A deposit with expectedHeld equal to the current holding succeeds for any caller; exact result. | Nitro-04, docs-0060-01 | Nitro:166-167 |
| `deposit_requires_expectedHeld` | `Safety.lean` | A deposit whose expectedHeld differs from the holding fails (compare-and-swap guard). | docs-0060-02 | go-nitro MultiAssetHolder.sol:51 |
| `deposit_respects_funding_order` | `Safety.lean` | A funder depositing with expectedHeld = allocations ahead of it succeeds only when they are held; its coins pay no entry ahead of it. | ForceMove-B07, docs-0060-02, docs-0060-06 | ForceMove:1197-1208 |
| `deposits_in_order_succeed` | `Safety.lean` | Deposits in pre-funding order with the correct expectedHeld all succeed and fully fund the channel. | ForceMove-C01, docs-0060-02 | ForceMove:1797-1808 |
| `deposit_to_external_fails` | `Safety.lean` | A deposit to an external destination fails (go-nitro). | Nitro-04, docs-0060-01 | go-nitro MultiAssetHolder.sol:43 |
| `held_falls_only_by_payout` | `Safety.lean` | On a reachable state, coins leave the contract only by a redistribution paying one external destination. | Nitro-06, Nitro-07, SATP-16 | go-nitro MultiAssetHolder.sol:402-415 |
| `channel_balance_falls_only_by_redistribution` | `Safety.lean` | A channel balance falls only by a redistribution. | Nitro-07 | Nitro:227-229 |
| `paid_out_monotone` | `Safety.lean` | Coins paid out to a participant are never taken back. | Nitro-06 | docs |
| `payout_priority_formula` | `Safety.lean` | Entry k is paid min(owed, held - total owed before k). | ForceMove-A16, ForceMove-B07, Nitro-26, SATP-12, docs-0080-03 | ForceMove:1837-1853 |
| `payout_earlier_paid_in_full` | `Safety.lean` | If a later entry is paid, every earlier entry is paid in full. | ForceMove-B07, Nitro-26, docs-0060-06 | ForceMove:1812-1821 |
| `payout_bounded` | `Safety.lean` | The payout never exceeds the coins held or an entry amount. | Nitro-26, Nitro-28, docs-0080-03 | docs |
| `paidTo_first_entry_only` | `Safety.lean` | A destination is paid at most its first entry. | Nitro-25 | Nitro:744-746 |
| `affords_when_fully_funded` | `Safety.lean` | A fully funded allocation affords every entry in full. | Nitro-16, Nitro-27 | Nitro:749-751 |
| `transfer_effects` | `Safety.lean` | On a reachable state, the transfer pays the affordable amount x: three effects (go-nitro, Nitro). | ForceMove-A15, Nitro-10, Nitro-28, docs-0030-03, docs-0080-03, docs-0080-04 | go-nitro MultiAssetHolder.sol:72-100 |
| `reduceOwed_owed` | `Safety.lean` | Reducing an owed amount is exact and local. | Nitro-28 | docs |
| `transfer_can_happen` | `Safety.lean` | A transfer on a finalized allocation entry succeeds and pays the affordable amount. | ForceMove-C03, Nitro-15, Nitro-28, docs-0080-06 | docs |
| `transfer_fails_otherwise` | `Safety.lean` | A transfer with no allocation entry (or a guarantee entry) fails. | ForceMove-A20, Nitro-29, docs-0030-04 | Nitro:771-772 |
| `transfer_zero_moves_nothing` | `Safety.lean` | A transfer that affords nothing changes no balance reading and no coins held. | Nitro-29 | docs |
| `transfer_requires_finalized` | `Safety.lean` | A transfer succeeds only on a finalized channel. | ForceMove-A15, Nitro-10, SATP-16, docs-0080-01 | Nitro:261-266 |
| `redistribution_ignores_caller` | `Safety.lean` | Transfer, claim and reclaim give the same result for every caller. | Nitro-15 | Nitro:312-313 |
| `redistribution_conserves_total` | `Safety.lean` | On a reachable state, redistribution keeps the sum of balances (held plus paid out). | Nitro-08 | docs |
| `finalized_two_ways` | `Safety.lean` | A finalized outcome came from a conclude or a timed-out challenge. | ForceMove-A14, ForceMove-B03, Nitro-11, SATP-16, docs-0070-04 | Nitro:770 |
| `finalized_permanent` | `Safety.lean` | A finalized channel stays finalized. | ForceMove-A14, ForceMove-D12, Nitro-14 | Nitro:301-302 |
| `finalized_outcome_only_redistributed` | `Safety.lean` | A finalized outcome is only ever redistributed, never replaced. | Nitro-14 | docs |
| `challenge_requires` | `Safety.lean` | A challenge needs a participant, support, and turn >= record (Open) or > record (Challenge). | ForceMove-A10, ForceMove-A21, SATP-14, docs-0070-02, docs-0070-03 | go-nitro ForceMove.sol:46-60 |
| `challenge_fails_when_finalized` | `Safety.lean` | A challenge on a finalized channel fails. | SATP-14 | go-nitro ForceMove.sol:52-54 |
| `rechallenge_equal_turn_fails` | `Safety.lean` | A re-challenge at an equal turn during a challenge fails (go-nitro; not SATP Listing 1). | SATP-14 | go-nitro ForceMove.sol:48-50 |
| `challenge_can_happen` | `Safety.lean` | A valid challenge succeeds with deadline now + duration; exact result. | ForceMove-A10, ForceMove-C02, ForceMove-F03, Nitro-12, SATP-14, docs-0070-08 | go-nitro ForceMove.sol:70-76 |
| `challenge_effects` | `Safety.lean` | A fresh challenge puts the channel in challenge mode and moves no coins. | ForceMove-B04, ForceMove-D12, SATP-14 | docs |
| `checkpoint_requires` | `Safety.lean` | A checkpoint needs a non-finalized channel, support and a strictly higher turn. | ForceMove-A11, ForceMove-A12, ForceMove-A13, ForceMove-A21, ForceMove-B02, docs-0070-10 | go-nitro ForceMove.sol:91-100 |
| `checkpoint_can_happen` | `Safety.lean` | A valid checkpoint reopens the channel at the new turn and clears a challenge. | ForceMove-A18, ForceMove-A21, ForceMove-B04, docs-0070-10 | ForceMove:1266-1269 |
| `turnNumRecord_monotone` | `Safety.lean` | No step lowers the stored turn number, except a conclude of the channel, which finalizes it. | ForceMove-A21, ForceMove-B02, docs-0040-03, docs-0070-03 | ForceMove:1543-1545 |
| `conclude_requires` | `Safety.lean` | A conclude needs a non-finalized channel, isFinal and unanimous signatures. | ForceMove-A14, Nitro-13, SATP-16, docs-0010-05, docs-0070-01 | SATP:288-289 |
| `conclude_needs_all` | `Safety.lean` | A conclude carries a state signed by every participant, for every app. | ForceMove-A09, Nitro-13, SATP-08, SATP-16, docs-0020-01, docs-0070-01 | go-nitro ForceMove.sol:147-152 |
| `conclude_can_happen` | `Safety.lean` | A conclusion proof finalizes at once with its outcome; exact result. | ForceMove-A14, Nitro-13, SATP-16, docs-0070-09 | Nitro:299-300 |
| `conclude_moves_no_value` | `Safety.lean` | A conclude moves no coins and no time. | ForceMove-A04, ForceMove-A05, docs-0070-07 | ForceMove:976-980 |
| `timeout_finalizes` | `Safety.lean` | A challenge past its deadline is finalized with the challenge outcome. | ForceMove-B03, ForceMove-D12, Nitro-12, docs-0040-05, docs-0040-06 | go-nitro StatusManager.sol:10-11 |
| `challenge_in_progress_before_deadline` | `Safety.lean` | A challenge before its deadline is in progress with no final outcome. | ForceMove-D12 | go-nitro StatusManager.sol:12-13 |
| `tick_moves_only_time` | `Safety.lean` | The clock changes no balance and no status. | ForceMove-F03, docs-0040-05 | docs |
| `failed_op_no_effect` | `Safety.lean` | A failed operation leaves the chain unchanged. | ForceMove-A20 | ForceMove:685-686 |
| `funding_decoupled_from_rules` | `Safety.lean` | The dispute operations do not read the balances. | ForceMove-F05 | go-nitro ForceMove.sol |
| `forceMove_supports_valid_run` | `Safety.lean` | A ForceMove support proof is a run of n valid moves signed by movers. | ForceMove-A01, ForceMove-A02, ForceMove-A03, ForceMove-D04, ForceMove-D05, ForceMove-D06 | go-nitro StrictTurnTaking.sol |
| `forceMove_conclude_keeps_outcome` | `Safety.lean` | A ForceMove conclude transition keeps the outcome; conclude is absorbing. | ForceMove-A04, ForceMove-A05, ForceMove-A08 | ForceMove:976-980 |
| `mover_determined_by_turn` | `Safety.lean` | The mover is a function of channel and turn number. | ForceMove-D05, ForceMove-D06 | ForceMove:724-727 |
| `mover_cyclic` | `Safety.lean` | Turns cycle with period n. | ForceMove-D06 | ForceMove:725-727 |
| `reclaim_requires` | `Safety.lean` | A reclaim needs both channels finalized, a guarantee entry, left/right entries, and matching amounts. | SATP-15, docs-0030-04 | SATP:348-352 |
| `reclaim_effects` | `Safety.lean` | A reclaim of a deduplicated ledger by another channel credits left and right from the target and deletes the guarantee. | SATP-15, docs-0080-05 | SATP:358-363 |
| `reclaim_can_happen` | `Safety.lean` | A reclaim with its preconditions succeeds; exact result. | SATP-15, docs-0080-05 | docs |
| `reclaim_fails_without_entries` | `Safety.lean` | A reclaim fails when left/right lack entries or the amounts mismatch (go-nitro). | SATP-15 | go-nitro MultiAssetHolder.sol:363-365 |
| `isOpen_iff` | `Safety.lean` | isOpen means open or challenge mode. | SATP-13, docs-0040-02 | SATP:294-298 |
| `mode_of_absent` | `Safety.lean` | A channel with no record is open at turn 0. | ForceMove-D11, Nitro-11 | docs |
| `held_changes_only_by_deposit_payout` | `Safety.lean` | Only a deposit or a redistribution changes the coins held. | Nitro-05, Nitro-08 | docs |
| `directly_funded_pays` | `Liveness.lean` | A directly funded finalized allocation pays p its entry with no wait. | ForceMove-A06, ForceMove-A07, ForceMove-B01, ForceMove-C03, Nitro-16, Nitro-21, Nitro-31, docs-0070-05, docs-0080-06 | Nitro:779-781 |
| `finalizable_funded_pays` | `Liveness.lean` | A finalizable allocation in a channel funded for p pays p its entry. | Nitro-16, Nitro-17, Nitro-21 | Nitro:480-481 |
| `conclusion_proof_finalizable` | `Liveness.lean` | A held conclusion proof makes its outcome finalizable with no wait. | ForceMove-A14, Nitro-13, Nitro-21, Nitro-23, docs-0070-05 | SATP:286-289 |
| `latest_state_finalizable` | `Liveness.lean` | The latest supported state is finalizable by challenge and timeout. | ForceMove-B01, ForceMove-B03, ForceMove-C02, Nitro-12, docs-0070-06 | SATP:290-292 |
| `late_observer_can_checkpoint` | `Liveness.lean` | A participant with a higher supported state can reopen a challenged channel. | ForceMove-B05 | ForceMove:1511-1529 |
| `finalizable_unique` | `Liveness.lean` | Two participants cannot each force different outcomes of one channel. | Nitro-22 | Nitro:612-614 |
| `channel_finalizability_cases` | `Liveness.lean` | A channel is in one of the four finalizability cases. | Nitro-22 | Nitro:597-611 |
| `finalizable_or_two_enabled` | `Liveness.lean` | A participant has a finalizable outcome or two enabled outcomes. | Nitro-21, Nitro-24 | Nitro:653-656 |
| `single_enabled_is_finalizable` | `Liveness.lean` | A single enabled outcome is finalizable. | Nitro-21, Nitro-24 | Nitro:657-658 |
| `funding_point_universally_finalizable` | `Liveness.lean` | At the funding point the outcome is universally finalizable. | ForceMove-A06, ForceMove-A07, ForceMove-B06, Nitro-23 | Nitro:635-636 |
| `concluded_universally_finalizable` | `Liveness.lean` | A concluded outcome is universally finalizable. | ForceMove-A14, Nitro-23 | Nitro:637-640 |
| `consensus_enabled_outcomes` | `Liveness.lean` | During a consensus transition only the old and new outcomes are enabled. | Nitro-49, SATP-08, docs-0020-01 | Nitro:660-688 |
| `turbo_redistribution_unbeatable` | `Liveness.lean` | In Turbo any transfer strategy that works is unbeatable. | Nitro-16, Nitro-30 | Nitro:775-777 |
| `deposit_bounds_value` | `Liveness.lean` | A deposit of y changes a value by between 0 and y. | Nitro-31 | Nitro:785-787 |
| `payout_to_other_affects_only_owner` | `Liveness.lean` | A payout to another participant leaves p's value unchanged. | Nitro-31 | Nitro:787-789 |
| `participant_can_prevent_cycles` | `Liveness.lean` | A participant can keep the outcome network acyclic. | Nitro-32 | Nitro:792-794 |
| `turbo_value_upper_bound` | `Liveness.lean` | On a DAG no strategy obtains more than the Turbo value. | Nitro-32, Nitro-33, Nitro-34 | Nitro:836-837 |
| `turbo_value_achievable` | `Liveness.lean` | On a DAG the Turbo value is obtainable. | Nitro-18, Nitro-33, Nitro-35 | Nitro:837-839 |
| `turbo_value_is_value` | `Liveness.lean` | The Turbo Value Algorithm computes the value of a network state. | Nitro-18, Nitro-33, Nitro-34, Nitro-35 | Nitro:482-484 |
| `turbo_order_independent` | `Liveness.lean` | Exhausted transfer sequences give the same balances. | Nitro-36 | Nitro:842-843 |
| `turbo_value_exists_unique` | `Liveness.lean` | On a DAG the Turbo value exists and is unique over all topological orders. | Nitro-32, Nitro-33, Nitro-36 | Nitro:819 |
| `ledger_offload_funds_subchannel` | `Liveness.lean` | A ledger channel funds its sub-channel for both participants. | Nitro-37, Nitro-47, docs-0060-07, docs-0080-08 | Nitro:859-865 |
| `subchannel_open_value_preserving` | `Liveness.lean` | Opening a sub-channel preserves value. | Nitro-49, docs-0060-07 | Nitro:891-922 |
| `subchannel_close_value_preserving` | `Liveness.lean` | Closing a sub-channel preserves value. | Nitro-49, docs-0080-07 | Nitro:939-957 |
| `ledger_topup_reorder_safe` | `Liveness.lean` | Moving A to the end of an underfunded ledger pays A the same. | Nitro-49, docs-0060-05 | Nitro:959-995 |
| `ledger_topup_deposit_funds` | `Liveness.lean` | After the top-up deposit every entry is affordable in full. | Nitro-04, Nitro-49, docs-0060-05 | Nitro:989-995 |
| `ledger_partial_withdrawal` | `Liveness.lean` | A partial withdrawal pays A with no wait and funds the new ledger. | Nitro-49 | Nitro:997-1047 |
| `satp_outcome_change_keeps_total` | `Liveness.lean` | validateOutcomeChange keeps the funded total of the start state. | SATP-18, SATP-19 | SATP:707-709 |
| `satp_lemma_3_1` | `Liveness.lean` | Lemma 3.1: V finalizes at version 0 with the original outcome or with the same total. | SATP-19, SATP-21 | SATP:511-513 |
| `satp_peers_can_finalize` | `Liveness.lean` | Lemma A.1: a peer can force V to finalize with the same total. | SATP-21 | SATP:747-750 |
| `satp_theorem_3_2` | `Liveness.lean` | Theorem 3.2: an honest intermediary recovers its ledger balances. | SATP-20 | SATP:503-507 |
| `satp_intermediary_before_round2` | `Liveness.lean` | Theorem 3.2 Cases 1-2: before Round 2 the intermediary keeps its balances. | SATP-20 | SATP:522-537 |
| `satp_end_user_recovers` | `Liveness.lean` | The end-user analogue of Theorem 3.2 for Alice. | SATP-20 | SATP:500-501 |
| `satp_reclaim_credits_intermediary` | `Liveness.lean` | Two reclaims credit the intermediary with a + b and delete the guarantees. | SATP-15, SATP-20 | SATP:484-485 |
