# Nitro specification repair, 2026-10-27 (for operator approval)

Branch `nitro-proofs`, base `aa52443`. Source: the defect report
`armada-laconic/labbook/2026-10-27-nitro-liveness-game-defects.md` (defects D1-D8, gaps G1-G13) and the
coordinator brief of 2026-10-27. Every theorem type that changed is listed in §4 with its old text, its new
text and the reason. `Safety.lean` stays proved. `Liveness.lean` stays `sorry`, except four theorems that read
no game definition. `ArmadaLean/Nitro/NonVacuity.lean` holds one proved witness per theorem with hypotheses
(verification.md §5a).

## 1. Destinations (operator ruling 2026-10-27)

- `Address E` has two constructors: `external (e : E)` and `channel (c : FixedPart)` (`Address.lean`). `E` is a
  type parameter of the whole specification. SATP:320-321, SATP:334-335: an outcome maps a destination to an
  item. go-nitro: a destination is a channel id or an external destination (MultiAssetHolder.sol:436
  `_isExternalDestination`). `Address.participant`, `Participant.address` and `Address.isParticipant` are
  removed; `Address.isExternal` replaces the last.
- The signers of a channel stay `FixedPart.participants`. A construction names the destination of each
  participant: `LedgerWithSub.dA`, `LedgerWithSub.dB`, `Route.dest`. `Route.WellFormed` requires distinct
  destinations of the peers.
- The SATP voucher outcome pays the first two destinations of the start state's outcome (`Outcome.pairDests`),
  because a participant is no longer a destination (`SATP.lean` module comment; SATP:705, SATP:710-717).
- `Value`, `SameValue` and `ValueIn` take the external destination `d` (Nitro:482-484 "the balance of A's address").

## 2. Game definitions

| Defect | Repair | File |
|---|---|---|
| D1 | `Assumptions` extends `Bounds` (unforgeable, unforgeableDeliver, notHonest) and `Capable` (capable, capableDeliver, capableTick). The Turbo game: `Threat.TransfersOnly` (transfers only, no tick), `Threat.CapableTransfers`, honest moves `HonestMove.IsTransfer`, strategies `UnbeatableIn … IsTransfer`, `CanObtainIn`, `ValueIn` (Nitro:779-781). | `Strategy.lean`, `Value.lean` |
| D2 | `SignedState.SignedIn signed`, `SignedStep`, `ReachableSigned apps signed s`: a history that uses only the signatures in `signed`, voucher signatures included (SATP:168, SATP:703). | `Adjudicator.lean` |
| D3 | `HonestMove.Feasible` is `False` for a deposit: `p` has no wallet, and Nitro:779-781 ignores deposits. | `Strategy.lean` |
| D4 | No separate repair: the clock rule below bounds every move of the clock in a round, the chain operation `tick` included. | `Strategy.lean` |
| D5 | `Strategy E p` is total. `Run` is a sequence of rounds (adversary prefix, then the move the strategy chose at the start of the round). `Prevents` asks for a strategy whose every move is feasible and whose every play, within rounds too, avoids the goal. | `Strategy.lean` |
| D6 | `ChannelStatus.finalized t f o`: `f` is the outcome of finalization (`ChannelStatus.finalizedWith`, `Adjudicator.finalizedWith`), `o` the stored outcome that `transfer` and `reclaim` rewrite (`finalOutcome`, unchanged meaning). `NetworkState.Finalized` reads `finalizedWith`. `withOutcome` keeps `f`. | `Channel.lean`, `Adjudicator.lean`, `Strategy.lean` |
| D7 | `forceMoveRules` also checks `byMover` of the first proof state (go-nitro StrictTurnTaking.sol:25-27 checks every proof state). `NetworkState.Holds` and `NetworkState.Unforged` cover the signers of a state's voucher: a voucher signature of `q` is a state `q` signed that carries the voucher. | `Channel.lean`, `Strategy.lean` |
| D8 | `Views.Consistent` has a third clause: a signature of `q` that `p` received is on a state `q` sent. | `Strategy.lean` |
| Clock | `Threat.ε` with `ε_pos : 0 < ε` (Nitro:537 "ε > 0"). `Threat.Round`: a feasible prefix that ends before `ε` has passed since the round began (Nitro:537-539 "before time t + ε"). `UnbeatableIn.move` and `Run.round` quantify over rounds. `Assumptions.unimpeded` and `NetworkState.PendingDeadline` are removed; `capableTick` allows any tick. `NetworkState.DeadlineAfter c δ`: a running challenge of `c` ends no sooner than `δ` from now. | `Strategy.lean` |

The clock rule and the duration bound. Nitro:537-539 gives a bound `ε` on inclusion. In the model `p` chooses
its move at the start of a round and the move lands before `ε` has passed. A challenge that the adversary
registers just after the start of a round is seen at the next round, and `p`'s answer lands before `2 * ε` has
passed since the challenge. So the liveness theorems assume `2 * ε ≤ challengeDuration`, not `ε <
challengeDuration` as the brief proposed: with `ε < challengeDuration` alone the adversary can register a
challenge at the start of a round and let it end before `p`'s answer to it lands. This replaces the approved
rule "only the honest `wait` reaches a deadline" (`docs/nitro-theorems.md`, "The game").

Other definition changes:
- `Value.lean` `payoutValues`: a guarantee item takes its place in the priority order and credits no one.
  `transfer` cannot pay a guarantee (go-nitro MultiAssetHolder.sol:169-170), and the Turbo game has no `reclaim`;
  with the old algorithm the value of a guarantee destination exceeded what any strategy obtains.
- `SATP.lean` `HoldsLatestLedger`: every other signed state of `L` has a lower turn or is the latest state (G2),
  `P` signed no final state of `L` (G6, the suspicion of the first audit), and the chain record of `L` is below
  the latest turn or is the latest state (G1; SATP:545-547 "held by anyone").
- `SATP.lean` `Route.LedgerAfterRound2 r o P Q D bal debit`: `D` names the debited peer (G14b, §4).
- `SATP.lean` `IntermediaryRecovered` and `EndUserRecovered` read the stored outcomes (the guarantee is removed
  there by `reclaim`, not in the outcome of finalization) and take `base`: the peer's destination balance when
  the strategy starts. The goal is `bal + base ≤ owed + balance`: a payout moves an owed amount to the balance.
- `Liveness.lean`: `UnbeatableNoWait` is `UnbeatableIn … HonestMove.NoWait`; new `SetupPhaseAccepted`;
  `Threat.TransfersOnly` moved to `Value.lean`.

## 3. Re-audit of the 35 Liveness theorems on the repaired model

Status: **proved** (no `sorry`); **sound** (true by the argument given, not yet proved; `[INFERENCE]`);
**unknown**; **false** (a counterexample by the argument given, `[INFERENCE]`; none is formalized).

| # | Theorem | Status | Argument or counterexample |
|---|---|---|---|
| 1 | `directly_funded_pays` | sound | `p` transfers to `d`. Every adversary step keeps the stored total at or below the holding and keeps `owed d + paid d` at or above its start. |
| 2 | `finalizable_funded_pays` | sound | Follow the `FundedFor` strategy; at its goal the stored total (a redistribution of the finalized one) is covered; then transfer to `d`. |
| 3 | `conclusion_proof_finalizable` | sound | `NonVacuity.conclude_strategy` proves this goal for any move class that allows the conclude (it is not wired into `Liveness.lean`). |
| 4 | `latest_state_finalizable` | sound | Challenge with `ss`, then wait. A higher record needs `p`'s signature on a higher state. |
| 5 | `late_observer_can_checkpoint` | sound | Checkpoint with `ss`; if the adversary registered `ss.state` first, the goal holds already. |
| 6 | `finalizable_unique` | proved | Joint play with one clock per participant (`finalizable_joint`, aln-a14). The calls of each participant run in the view of the other as adversary moves; a `wait` moves only its own clock. The status of `c` agrees on both chains up to the deadline of a running challenge. When both wait, `q` waits first if the running challenge pays `Ω`, else `p` waits first, so the first chain that finalizes `c` gives `Ω = Ω'` or contradicts a strategy. |
| 7 | `channel_finalizability_cases` | unknown | Follows from 6 by a case split. |
| 8 | `finalizable_or_two_enabled` | unknown | A determinacy argument; not checked. |
| 9 | `single_enabled_is_finalizable` | unknown | As 8. |
| 10 | `finalizable_is_enabled` | removed | `c = [p]`, fresh: `p` finalizes by `send` then `conclude`; `p` also prevents every finalization by signing nothing. "Can force" and "cannot prevent" differ whenever the outcome needs `p`'s signature. Coordinator ruling 2026-10-27 (§6.1): Nitro 2019 §4.4's dichotomy (finalizable or two enabled) never claims finalizable implies enabled; the theorem is removed, not repaired. |
| 11 | `funding_point_universally_finalizable` | false | New defect D9 below: with `n = 2` and a game library that accepts a move after the setup, the adversary challenges with a state at turn `n` that it never delivers; `p` cannot answer it. |
| 12 | `concluded_universally_finalizable` | sound | `conclude_strategy` for each participant. |
| 13 | `consensus_enabled_outcomes` | sound | `p`'s strategy answers every challenge below `ss` with `ss` within `2 * ε`; only `Ω1`, `Ω2` can finalize. |
| 14 | `turbo_redistribution_unbeatable` | unknown | Believed true (priority payouts are monotone). |
| 15 | `deposit_bounds_value` | unknown | Needs a coupling of plays with and without the deposit. |
| 16 | `payout_to_other_affects_only_owner` | unknown | As 15. |
| 17 | `participant_can_prevent_cycles` | sound | `p` never signs; under consensus no channel of `p` can leave Open. |
| 18 | `turbo_value_upper_bound` | unknown | Believed true. |
| 19 | `turbo_value_achievable` | unknown | Believed true. |
| 20 | `turbo_value_is_value` | unknown | From 18 and 19. |
| 21 | `turbo_order_independent` | unknown | Believed true; reads no game definition. |
| 22 | `turbo_value_exists_unique` | unknown | Believed true; reads no game definition. |
| 23 | `ledger_offload_funds_subchannel` | false | If `χ` is finalized with an outcome that pays elsewhere, the adversary transfers `L → χ` and `χ → q` in one prefix; `χ` never holds `c` at a round boundary. Needs the G16 hypotheses of `ledger_partial_withdrawal` for `χ` (type change; not applied: not in the report). |
| 24 | `subchannel_open_value_preserving` | unknown | Value equality; not checked. |
| 25 | `subchannel_close_value_preserving` | unknown | As 24. |
| 26 | `ledger_topup_reorder_safe` | proved | Priority payout arithmetic. |
| 27 | `ledger_topup_deposit_funds` | proved | Priority payout arithmetic. |
| 28 | `ledger_partial_withdrawal` | sound | Conclude `L`, then transfer: two rounds without wait; `L'` cannot finalize within them. |
| 29 | `satp_outcome_change_keeps_total` | proved | Case split on the proof; helpers `validChallenge_outcome`, `validResponse_outcome`. |
| 30 | `satp_lemma_3_1` | sound | `finalized_two_ways` over `ReachableSigned`; every all-signed state of `V` is a setup state or a final pair; a challenge or response state pays the start state's destinations with the total. |
| 31 | `satp_peers_can_finalize` | false | D9: the adversary checkpoints `V` with a response at version 3 that it never delivers; `V` stays Open at record 3 and `p` holds no supported state at version 3 or above. |
| 32 | `satp_theorem_3_2` | false | D9 as in 31, so `V` may never finalize; and the reclaim griefing G17 below. |
| 33 | `satp_intermediary_before_round2` | sound | Challenge both ledgers with the latest states, then wait; the goal counts payouts. |
| 34 | `satp_end_user_recovers` | false | G17: the adversary deposits into `V` and transfers from `V`, which lowers `V`'s stored amounts; `reclaim` then reverts for ever (MultiAssetHolder.sol:365). |
| 35 | `satp_reclaim_credits_intermediary` | proved | `reclaim_can_happen` twice and the `owed` lemmas. |

Counts: proved 4, sound 11, unknown 14, false 5, removed 1 (§6.1).

### New defects found by the re-audit

- **D9. The honest participant does not see the states submitted on-chain.** go-nitro emits the signed states of
  a challenge (`ChallengeRegistered`) and a checkpoint is calldata. In the model `p` can use a state only if it
  is in `sent` or `received`, so an adversary that registers a state and does not deliver it gains a move that
  `p` cannot answer (theorems 11, 31, 32). Proposed repair: `applyAdv (.chain caller op)` adds `op.proofStates` to
  `received` when the operation succeeds. This changes a definition only.
- **G15.** A channel target can pay its coins onward in the same round (theorems 14, 19, 23): applied to 14 and
  19 (external targets only); 23 is not changed.
- **G16.** A channel that receives funds must not finalize during the strategy (applied to 28, not to 23).
- **G17. Reclaim griefing.** go-nitro `reclaim` requires `o_target[0] + o_target[1] = x` on the stored outcome of
  the target (MultiAssetHolder.sol:365), and `transfer` rewrites that outcome (`_updateFingerprint`). Anyone can
  deposit into a finalized virtual channel and pay out of it; then the sum is below the guarantee amount and the
  reclaim reverts for ever. Reproduced against go-nitro `64c4ee9a1` (armada-laconic
  `labbook/2026-10-27-gonitro-reclaim-dos.md`). Theorems 32 and 34 depended on it. **Repaired by §6.3** (operator
  ruling 2026-10-27): `deposit` and `transfer` succeed only for a ledger channel, and `reclaim` reads the target's
  `finalizedWith` outcome (SATP:335-338). The 2026-10-29 re-audit found 32 and 34 true under the current model
  (argument, not proved).
- **G14.** `finalizable_funded_pays` composed a finalize strategy and a fund strategy from the same start
  (applied: the channel is finalized already). **G14b.** `LedgerAfterRound2 om Pprev P` debited `Pprev`, while
  the goal read `P`'s entry (applied).

## 4. Theorem types that changed

Every theorem of `Safety.lean` and `Liveness.lean` changed type at least by the parameter `E`.

### `Safety.lean`

Type changed by the parameter `E` only (55): `balances_absent_zero`, `held_eq_channel_balances`, `balances_total_split`, `deposit_effects`, `deposit_can_happen`, `deposit_requires_expectedHeld`, `deposit_respects_funding_order`, `deposits_in_order_succeed`, `channel_balance_falls_only_by_redistribution`, `payout_priority_formula`, `payout_earlier_paid_in_full`, `payout_bounded`, `paidTo_first_entry_only`, `affords_when_fully_funded`, `reduceOwed_owed`, `transfer_can_happen`, `transfer_fails_otherwise`, `transfer_zero_moves_nothing`, `transfer_requires_finalized`, `redistribution_ignores_caller`, `redistribution_conserves_total`, `FinalizedTwoWays.mono`, `statusOrigin_of_eq`, `statusOrigin_step`, `statusOrigin_reachable`, `finalized_two_ways`, `finalized_permanent`, `finalized_outcome_only_redistributed`, `challenge_requires`, `challenge_fails_when_finalized`, `rechallenge_equal_turn_fails`, `challenge_can_happen`, `challenge_effects`, `checkpoint_requires`, `checkpoint_can_happen`, `turnNumRecord_monotone`, `conclude_requires`, `conclude_needs_all`, `conclude_moves_no_value`, `timeout_finalizes`, `challenge_in_progress_before_deadline`, `tick_moves_only_time`, `failed_op_no_effect`, `funding_decoupled_from_rules`, `forceMove_supports_valid_run`, `forceMove_conclude_keeps_outcome`, `mover_determined_by_turn`, `mover_cyclic`, `reclaim_requires`, `reclaim_effects`, `reclaim_can_happen`, `reclaim_fails_without_entries`, `isOpen_iff`, `mode_of_absent`, `held_changes_only_by_deposit_payout`.

The change in each of these is mechanical: a type `X` of the model becomes `X E` (`Adjudicator E`, `Allocation E`, `Threat E p`, …). The old and new texts are equal after that rewrite (checked by a comparison of the signatures at `aa52443` and now, with the rewrite undone and whitespace collapsed).

#### `channel_address_inj`

D-E. The address type has the parameter `E`; the hypothesis names it (`(c.address : Address E)`).

Old (`aa52443`):

```lean
theorem channel_address_inj(c c' : FixedPart) (h : c.address = c'.address) : c = c'
```

New:

```lean
theorem channel_address_inj(c c' : FixedPart) (h : (c.address : Address E) = c'.address) : c = c'
```

#### `channel_address_ne_external`

D-E. Replaces `channel_address_ne_participant`: a channel id is never an external destination (go-nitro MultiAssetHolder.sol:436).

Old: none (new theorem).

New:

```lean
theorem channel_address_ne_external(c : FixedPart) (e : E) : c.address ≠ Address.external e
```

#### `deposit_to_external_fails`

D-E. Replaces `deposit_to_participant_fails` (go-nitro MultiAssetHolder.sol:43).

Old: none (new theorem).

New:

```lean
theorem deposit_to_external_fails(s : Adjudicator E) (d : E) (e x : Coins) : s.deposit (.external d) e x = none
```

#### `held_falls_only_by_payout`

D-E. The paid destination is an external destination `d : E`, not a participant.

Old (`aa52443`):

```lean
theorem held_falls_only_by_payout(apps : Apps) (s s' : Adjudicator) (hr : Reachable apps s) (caller : Participant) (op : Op) (h : s.apply apps caller op = some s') (hlt : s'.held < s.held) : op.isRedistribution = true ∧ ∃ p, s'.balances.get (.participant p) = s.balances.get (.participant p) + (s.held - s'.held) ∧ ∀ q, q ≠ p → s'.balances.get (.participant q) = s.balances.get (.participant q)
```

New:

```lean
theorem held_falls_only_by_payout(apps : Apps E) (s s' : Adjudicator E) (hr : Reachable apps s) (caller : Participant) (op : Op E) (h : s.apply apps caller op = some s') (hlt : s'.held < s.held) : op.isRedistribution = true ∧ ∃ d : E, s'.balances.get (.external d) = s.balances.get (.external d) + (s.held - s'.held) ∧ ∀ d', d' ≠ d → s'.balances.get (.external d') = s.balances.get (.external d')
```

#### `paid_out_monotone`

D-E. The destination is an external destination `d : E`.

Old (`aa52443`):

```lean
theorem paid_out_monotone(apps : Apps) (s s' : Adjudicator) (h : Step apps s s') (p : Participant) : s.balances.get (.participant p) ≤ s'.balances.get (.participant p)
```

New:

```lean
theorem paid_out_monotone(apps : Apps E) (s s' : Adjudicator E) (h : Step apps s s') (d : E) : s.balances.get (.external d) ≤ s'.balances.get (.external d)
```

#### `transfer_effects`

D-E. `Address.isParticipant` is renamed `Address.isExternal` (go-nitro `_isExternalDestination`).

Old (`aa52443`):

```lean
theorem transfer_effects(apps : Apps) (s : Adjudicator) (hr : Reachable apps s) (a : FixedPart) (b : Address) (s' : Adjudicator) (h : s.transfer a b = some s') : ∃ o x, s.finalOutcome a.address = some (.allocation o) ∧ x = o.paidTo (s.balances.get a.address) b ∧ s'.balances.get a.address + x = s.balances.get a.address + (if b = a.address then x else 0) ∧ (b ≠ a.address → s'.balances.get b = s.balances.get b + x) ∧ (∀ d, d ≠ a.address → d ≠ b → s'.balances.get d = s.balances.get d) ∧ s'.finalOutcome a.address = some (.allocation (o.reduceOwed b x)) ∧ s'.held + (if b.isParticipant then x else 0) = s.held ∧ s'.now = s.now
```

New:

```lean
theorem transfer_effects(apps : Apps E) (s : Adjudicator E) (hr : Reachable apps s) (a : FixedPart) (b : Address E) (s' : Adjudicator E) (h : s.transfer a b = some s') : ∃ o x, s.finalOutcome a.address = some (.allocation o) ∧ x = o.paidTo (s.balances.get a.address) b ∧ s'.balances.get a.address + x = s.balances.get a.address + (if b = a.address then x else 0) ∧ (b ≠ a.address → s'.balances.get b = s.balances.get b + x) ∧ (∀ d, d ≠ a.address → d ≠ b → s'.balances.get d = s.balances.get d) ∧ s'.finalOutcome a.address = some (.allocation (o.reduceOwed b x)) ∧ s'.held + (if b.isExternal then x else 0) = s.held ∧ s'.now = s.now
```

#### `statusOrigin_redistribute`

D6 (helper theorem). A finalized status now keeps two outcomes; the hypothesis `hs` says the new status is `(s.statusOf c).withOutcome Ω'` instead of naming the constructor, and the unused binder `t` is gone.

Old (`aa52443`):

```lean
theorem statusOrigin_redistribute{apps : Apps} {s s' : Adjudicator} {c : FixedPart} {Ω Ω' : Outcome} {t : Nat} (ho : StatusOrigin apps s c) (hf : (s.statusOf c).finalOutcome s.now = some Ω) (hR : Redistributed Ω Ω') (hn : s.now ≤ s'.now) (hs : s'.statusOf c = .finalized t Ω') : StatusOrigin apps s' c
```

New:

```lean
theorem statusOrigin_redistribute{apps : Apps E} {s s' : Adjudicator E} {c : FixedPart} {Ω Ω' : Outcome E} (ho : StatusOrigin apps s c) (hf : (s.statusOf c).finalOutcome s.now = some Ω) (hR : Redistributed Ω Ω') (hn : s.now ≤ s'.now) (hs : s'.statusOf c = (s.statusOf c).withOutcome Ω') : StatusOrigin apps s' c
```

#### `conclude_can_happen`

D6. `ChannelStatus.finalized` has a second outcome field (the outcome of finalization); a conclude sets both to the candidate's outcome.

Old (`aa52443`):

```lean
theorem conclude_can_happen(s : Adjudicator) (c : FixedPart) (ss : SignedState) (hm : s.mode c ≠ .finalized) (hproof : ConclusionProof c ss) : s.conclude c ss = some (s.setStatus c (.finalized ss.state.turnNum ss.state.outcome)) ∧ (s.setStatus c (.finalized ss.state.turnNum ss.state.outcome)).finalOutcome c.address = some ss.state.outcome ∧ (s.setStatus c (.finalized ss.state.turnNum ss.state.outcome)).mode c = .finalized
```

New:

```lean
theorem conclude_can_happen(s : Adjudicator E) (c : FixedPart) (ss : SignedState E) (hm : s.mode c ≠ .finalized) (hproof : ConclusionProof c ss) : s.conclude c ss = some (s.setStatus c (.finalized ss.state.turnNum ss.state.outcome ss.state.outcome)) ∧ (s.setStatus c (.finalized ss.state.turnNum ss.state.outcome ss.state.outcome)).finalOutcome c.address = some ss.state.outcome ∧ (s.setStatus c (.finalized ss.state.turnNum ss.state.outcome ss.state.outcome)).mode c = .finalized
```

#### `deposit_to_participant_fails`

D-E. Removed with `Address.participant`. Replaced by `deposit_to_external_fails`.

Old (`aa52443`):

```lean
theorem deposit_to_participant_fails(s : Adjudicator) (p : Participant) (e x : Coins) : s.deposit (.participant p) e x = none
```

New: removed.

#### `channel_address_ne_participant`

D-E. Removed: `Address.participant` is no longer a destination (operator ruling 2026-10-27). Replaced by `channel_address_ne_external`.

Old (`aa52443`):

```lean
theorem channel_address_ne_participant(c : FixedPart) (p : Participant) : c.address ≠ .participant p
```

New: removed.

### `Liveness.lean`

Type changed by the parameter `E` only (8): `finalizable_unique`, `channel_finalizability_cases`, `finalizable_is_enabled`, `turbo_order_independent`, `turbo_value_exists_unique`, `ledger_offload_funds_subchannel`, `ledger_topup_reorder_safe`, `ledger_topup_deposit_funds`.

The change in each of these is mechanical: a type `X` of the model becomes `X E` (`Adjudicator E`, `Allocation E`, `Threat E p`, …). The old and new texts are equal after that rewrite (checked by a comparison of the signatures at `aa52443` and now, with the rewrite undone and whitespace collapsed).

#### `directly_funded_pays`

D-E, G11. `hf` reads the stored outcome (`finalOutcome`, which `transfer` reads) instead of `Finalized` (D6). `p.address` becomes the external destination `d`. New `amt`, `hd`: the first entry of `d` is an allocation item; go-nitro refuses to transfer a guarantee (MultiAssetHolder.sol:169-170).

Old (`aa52443`):

```lean
theorem directly_funded_pays(apps : Apps) {p : Participant} (T : Threat p) (A : Assumptions apps p T) (net : NetworkState p) (c : FixedPart) (o : Allocation) (hf : net.Finalized c (.allocation o)) (hfund : net.chain.DirectlyFunded c) : UnbeatableNoWait apps T (fun net' => net.chain.balances.get p.address + o.owed p.address ≤ net'.chain.balances.get p.address) net
```

New:

```lean
theorem directly_funded_pays(apps : Apps E) {p : Participant} (T : Threat E p) (A : Assumptions apps p T) (net : NetworkState E p) (c : FixedPart) (o : Allocation E) (d : E) (hf : net.chain.finalOutcome c.address = some (.allocation o)) (hfund : net.chain.DirectlyFunded c) (amt : Coins) (hd : o.find (.external d) = some ⟨.external d, .alloc amt⟩) : UnbeatableNoWait apps T (fun net' => net.chain.balances.get (.external d) + o.owed (.external d) ≤ net'.chain.balances.get (.external d)) net
```

#### `finalizable_funded_pays`

D-E, G11, new gap G14. `hf` was `Finalizable`; a finalize strategy and a fund strategy do not compose because each starts from `net`, so `hf` now says the channel is finalized (stored outcome). `d` replaces `p.address`; `hd` as in `directly_funded_pays`.

Old (`aa52443`):

```lean
theorem finalizable_funded_pays(apps : Apps) {p : Participant} (T : Threat p) (A : Assumptions apps p T) (net : NetworkState p) (c : FixedPart) (o : Allocation) (hf : Finalizable apps T c (.allocation o) net) (hfund : FundedFor apps T c o.total net) : CanObtain apps T p.address (net.chain.balances.get p.address + o.owed p.address) net
```

New:

```lean
theorem finalizable_funded_pays(apps : Apps E) {p : Participant} (T : Threat E p) (A : Assumptions apps p T) (net : NetworkState E p) (c : FixedPart) (o : Allocation E) (d : E) (hf : net.chain.finalOutcome c.address = some (.allocation o)) (hfund : FundedFor apps T c o.total net) (amt : Coins) (hd : o.find (.external d) = some ⟨.external d, .alloc amt⟩) : CanObtain apps T (.external d) (net.chain.balances.get (.external d) + o.owed (.external d)) net
```

#### `conclusion_proof_finalizable`

D-E, D6, G3, clock. `hchain` reads the outcome of finalization. New `hdur : 2 * T.ε ≤ c.challengeDuration` and `hpend : net.DeadlineAfter c T.ε`: no challenge that the adversary registers or that is running can end before `p`'s conclude lands (Nitro:537-539).

Old (`aa52443`):

```lean
theorem conclusion_proof_finalizable(apps : Apps) {p : Participant} (T : Threat p) (A : Assumptions apps p T) (net : NetworkState p) (c : FixedPart) (ss : SignedState) (Ω : Outcome) (hc : apps c.appDef = consensusRules) (hp : p ∈ c.participants) (hh : net.Holds ss) (hproof : ConclusionProof c ss) (hΩ : ss.state.outcome = Ω) (hsent : ∀ t ∈ net.sent, t.state.channel = c → t.state.isFinal = true → t.state.outcome = Ω) (hchain : net.chain.finalOutcome c.address = none ∨ net.chain.finalOutcome c.address = some Ω) : UnbeatableNoWait apps T (fun net' => net'.Finalized c Ω) net
```

New:

```lean
theorem conclusion_proof_finalizable(apps : Apps E) {p : Participant} (T : Threat E p) (A : Assumptions apps p T) (net : NetworkState E p) (c : FixedPart) (ss : SignedState E) (Ω : Outcome E) (hc : apps c.appDef = consensusRules) (hp : p ∈ c.participants) (hh : net.Holds ss) (hproof : ConclusionProof c ss) (hΩ : ss.state.outcome = Ω) (hsent : ∀ t ∈ net.sent, t.state.channel = c → t.state.isFinal = true → t.state.outcome = Ω) (hchain : net.chain.finalizedWith c.address = none ∨ net.Finalized c Ω) (hdur : 2 * T.ε ≤ c.challengeDuration) (hpend : net.DeadlineAfter c T.ε) : UnbeatableNoWait apps T (fun net' => net'.Finalized c Ω) net
```

#### `latest_state_finalizable`

D-E, G1, G2, clock. `hlatest` is strict or the same state (go-nitro ForceMove.sol:48-50: an equal turn cannot override). `hdur` is `2 * T.ε`. `hrec` and `hchain` become `hst`: the chain record is at or below the state, or is that state, or the channel is finalized with its outcome; a running challenge ends no sooner than `ε` from now.

Old (`aa52443`):

```lean
theorem latest_state_finalizable(apps : Apps) {p : Participant} (T : Threat p) (A : Assumptions apps p T) (net : NetworkState p) (c : FixedPart) (ss : SignedState) (hc : apps c.appDef = consensusRules) (hp : p ∈ c.participants) (hh : net.Holds ss) (hall : ss.ByAll) (hchan : ss.state.channel = c) (hlatest : ∀ t ∈ net.sent, t.state.channel = c → t.state.turnNum ≤ ss.state.turnNum) (hfinal : ∀ t ∈ net.sent, t.state.channel = c → t.state.isFinal = true → t.state.outcome = ss.state.outcome) (hdur : 0 < c.challengeDuration) (hrec : (net.chain.statusOf c).turnNumRecord ≤ ss.state.turnNum) (hchain : net.chain.finalOutcome c.address = none ∨ net.chain.finalOutcome c.address = some ss.state.outcome) : Finalizable apps T c ss.state.outcome net
```

New:

```lean
theorem latest_state_finalizable(apps : Apps E) {p : Participant} (T : Threat E p) (A : Assumptions apps p T) (net : NetworkState E p) (c : FixedPart) (ss : SignedState E) (hc : apps c.appDef = consensusRules) (hp : p ∈ c.participants) (hh : net.Holds ss) (hall : ss.ByAll) (hchan : ss.state.channel = c) (hlatest : ∀ t ∈ net.sent, t.state.channel = c → t.state.turnNum < ss.state.turnNum ∨ t.state = ss.state) (hfinal : ∀ t ∈ net.sent, t.state.channel = c → t.state.isFinal = true → t.state.outcome = ss.state.outcome) (hdur : 2 * T.ε ≤ c.challengeDuration) (hst : net.Finalized c ss.state.outcome ∨ (∃ t, net.chain.statusOf c = .open t ∧ t ≤ ss.state.turnNum) ∨ (∃ t ch, net.chain.statusOf c = .challenged t ch ∧ (t < ss.state.turnNum ∨ ch.state = ss.state) ∧ net.chain.now + T.ε ≤ ch.deadline)) : Finalizable apps T c ss.state.outcome net
```

#### `late_observer_can_checkpoint`

D-E, G3, G5, clock. New `hp`, `hsent` (no signed state above `ss`, none final), `hdur`; `hnow` is `now + ε ≤ deadline`. The goal is 'not finalized and the record reaches the state's turn': the adversary can register `ss`'s own state as a challenge, so Open mode cannot be forced (ForceMove:1511-1529 says the moves 'still stand').

Old (`aa52443`):

```lean
theorem late_observer_can_checkpoint(apps : Apps) {p : Participant} (T : Threat p) (A : Assumptions apps p T) (net : NetworkState p) (c : FixedPart) (ss : SignedState) (t : Nat) (ch : Challenge) (hc : apps c.appDef = consensusRules) (hh : net.Holds ss) (hall : ss.ByAll) (hchan : ss.state.channel = c) (hst : net.chain.statusOf c = .challenged t ch) (hgt : t < ss.state.turnNum) (hnow : net.chain.now < ch.deadline) : UnbeatableNoWait apps T (fun net' => net'.chain.mode c = .open ∧ ss.state.turnNum ≤ (net'.chain.statusOf c).turnNumRecord) net
```

New:

```lean
theorem late_observer_can_checkpoint(apps : Apps E) {p : Participant} (T : Threat E p) (A : Assumptions apps p T) (net : NetworkState E p) (c : FixedPart) (ss : SignedState E) (t : Nat) (ch : Challenge E) (hc : apps c.appDef = consensusRules) (hp : p ∈ c.participants) (hh : net.Holds ss) (hall : ss.ByAll) (hchan : ss.state.channel = c) (hsent : ∀ u ∈ net.sent, u.state.channel = c → (u.state.turnNum < ss.state.turnNum ∨ u.state = ss.state) ∧ u.state.isFinal = false) (hst : net.chain.statusOf c = .challenged t ch) (hgt : t < ss.state.turnNum) (hnow : net.chain.now + T.ε ≤ ch.deadline) (hdur : 2 * T.ε ≤ c.challengeDuration) : UnbeatableNoWait apps T (fun net' => net'.chain.mode c ≠ .finalized ∧ ss.state.turnNum ≤ (net'.chain.statusOf c).turnNumRecord) net
```

#### `finalizable_or_two_enabled`

D-E, G12, clock. New `hsupp`: `p` holds a supported state of `c` (the channel is past its setup; Nitro:653-656); new `hdur`. `A` and `hp` are kept.

Old (`aa52443`):

```lean
theorem finalizable_or_two_enabled(apps : Apps) {p : Participant} (T : Threat p) (A : Assumptions apps p T) (net : NetworkState p) (c : FixedPart) (hp : p ∈ c.participants) : (∃ Ω, Finalizable apps T c Ω net) ∨ (∃ Ω1 Ω2, Ω1 ≠ Ω2 ∧ Enabled apps T c Ω1 net ∧ Enabled apps T c Ω2 net)
```

New:

```lean
theorem finalizable_or_two_enabled(apps : Apps E) {p : Participant} (T : Threat E p) (A : Assumptions apps p T) (net : NetworkState E p) (c : FixedPart) (hp : p ∈ c.participants) (hsupp : ∃ proof candidate, (∀ ss ∈ proof, net.Holds ss) ∧ (apps c.appDef).supports c proof candidate = true ∧ candidate.channel = c) (hdur : 2 * T.ε ≤ c.challengeDuration) : (∃ Ω, Finalizable apps T c Ω net) ∨ (∃ Ω1 Ω2, Ω1 ≠ Ω2 ∧ Enabled apps T c Ω1 net ∧ Enabled apps T c Ω2 net)
```

#### `single_enabled_is_finalizable`

D-E, G13, clock. New `hsupp`: `p` holds a support for every state of `c` it signed; new `hdur`.

Old (`aa52443`):

```lean
theorem single_enabled_is_finalizable(apps : Apps) {p : Participant} (T : Threat p) (A : Assumptions apps p T) (net : NetworkState p) (c : FixedPart) (hp : p ∈ c.participants) (Ω : Outcome) (hΩ : Enabled apps T c Ω net) (huniq : ∀ Ω', Enabled apps T c Ω' net → Ω' = Ω) : Finalizable apps T c Ω net
```

New:

```lean
theorem single_enabled_is_finalizable(apps : Apps E) {p : Participant} (T : Threat E p) (A : Assumptions apps p T) (net : NetworkState E p) (c : FixedPart) (hp : p ∈ c.participants) (hsupp : ∀ t ∈ net.sent, t.state.channel = c → ∃ proof, (∀ ss ∈ proof, net.Holds ss) ∧ (apps c.appDef).supports c proof t.state = true) (hdur : 2 * T.ε ≤ c.challengeDuration) (Ω : Outcome E) (hΩ : Enabled apps T c Ω net) (huniq : ∀ Ω', Enabled apps T c Ω' net → Ω' = Ω) : Finalizable apps T c Ω net
```

#### `funding_point_universally_finalizable`

D-E, G9, clock. New `hvt : SetupPhaseAccepted vt c` (the game library accepts the setup transitions, ForceMove:1092-1125). `hdur` is `2 * ε` for each participant's threat.

Old (`aa52443`):

```lean
theorem funding_point_universally_finalizable(apps : Apps) (Ts : Threats apps) (v : Views) (hv : v.Consistent) (c : FixedPart) (Ω : Outcome) (vt : State → State → Bool) (hc : apps c.appDef = forceMoveRules vt) (hsetup : SetupPhaseKeepsOutcome vt c) (hn : 0 < c.n) (hdur : 0 < c.challengeDuration) (h : AtFundingPoint v c Ω) (hchain : ∀ p, (v p).chain.mode c = .open ∧ (v p).chain.statusOf c = .open 0) : UniversallyFinalizable apps Ts v c Ω
```

New:

```lean
theorem funding_point_universally_finalizable(apps : Apps E) (Ts : Threats E apps) (v : Views E) (hv : v.Consistent) (c : FixedPart) (Ω : Outcome E) (vt : State E → State E → Bool) (hc : apps c.appDef = forceMoveRules vt) (hsetup : SetupPhaseKeepsOutcome vt c) (hvt : SetupPhaseAccepted vt c) (hn : 0 < c.n) (hdur : ∀ p, 2 * (Ts.T p).ε ≤ c.challengeDuration) (h : AtFundingPoint v c Ω) (hchain : ∀ p, (v p).chain.mode c = .open ∧ (v p).chain.statusOf c = .open 0) : UniversallyFinalizable apps Ts v c Ω
```

#### `concluded_universally_finalizable`

D-E, D6, G3, clock. `hchain` reads the outcome of finalization; new `hdur` and `hpend` per participant, as in `conclusion_proof_finalizable`.

Old (`aa52443`):

```lean
theorem concluded_universally_finalizable(apps : Apps) (Ts : Threats apps) (v : Views) (hv : v.Consistent) (c : FixedPart) (Ω : Outcome) (hc : apps c.appDef = consensusRules) (h : Concluded v c Ω) (hsent : ∀ p, ∀ t ∈ (v p).sent, t.state.channel = c → t.state.isFinal = true → t.state.outcome = Ω) (hchain : ∀ p, (v p).chain.finalOutcome c.address = none ∨ (v p).chain.finalOutcome c.address = some Ω) : UniversallyFinalizable apps Ts v c Ω
```

New:

```lean
theorem concluded_universally_finalizable(apps : Apps E) (Ts : Threats E apps) (v : Views E) (hv : v.Consistent) (c : FixedPart) (Ω : Outcome E) (hc : apps c.appDef = consensusRules) (h : Concluded v c Ω) (hsent : ∀ p, ∀ t ∈ (v p).sent, t.state.channel = c → t.state.isFinal = true → t.state.outcome = Ω) (hchain : ∀ p, (v p).chain.finalizedWith c.address = none ∨ (v p).Finalized c Ω) (hdur : ∀ p, 2 * (Ts.T p).ε ≤ c.challengeDuration) (hpend : ∀ p, (v p).DeadlineAfter c (Ts.T p).ε) : UniversallyFinalizable apps Ts v c Ω
```

#### `consensus_enabled_outcomes`

D-E, G1, G2, G4, clock. `hsent` is strict or the same state or outcome `Ω2`, and every final signed state has `Ω1` or `Ω2`. `hchain` becomes `hst` (chain record at or below the state, a running challenge ends no sooner than `ε`). New `hdur`.

Old (`aa52443`):

```lean
theorem consensus_enabled_outcomes(apps : Apps) {p : Participant} (T : Threat p) (A : Assumptions apps p T) (net : NetworkState p) (c : FixedPart) (ss : SignedState) (Ω1 Ω2 : Outcome) (hc : apps c.appDef = consensusRules) (hp : p ∈ c.participants) (hh : net.Holds ss) (hall : ss.ByAll) (hchan : ss.state.channel = c) (hΩ1 : ss.state.outcome = Ω1) (hsent : ∀ t ∈ net.sent, t.state.channel = c → t.state.turnNum ≤ ss.state.turnNum ∨ t.state.outcome = Ω2) (hchain : net.chain.finalOutcome c.address = none) (Ω : Outcome) (hen : Enabled apps T c Ω net) : Ω = Ω1 ∨ Ω = Ω2
```

New:

```lean
theorem consensus_enabled_outcomes(apps : Apps E) {p : Participant} (T : Threat E p) (A : Assumptions apps p T) (net : NetworkState E p) (c : FixedPart) (ss : SignedState E) (Ω1 Ω2 : Outcome E) (hc : apps c.appDef = consensusRules) (hp : p ∈ c.participants) (hh : net.Holds ss) (hall : ss.ByAll) (hchan : ss.state.channel = c) (hΩ1 : ss.state.outcome = Ω1) (hsent : ∀ t ∈ net.sent, t.state.channel = c → (t.state.turnNum < ss.state.turnNum ∨ t.state = ss.state ∨ t.state.outcome = Ω2) ∧ (t.state.isFinal = true → t.state.outcome = Ω1 ∨ t.state.outcome = Ω2)) (hdur : 2 * T.ε ≤ c.challengeDuration) (hst : (∃ t, net.chain.statusOf c = .open t ∧ t ≤ ss.state.turnNum) ∨ (∃ t ch, net.chain.statusOf c = .challenged t ch ∧ (t < ss.state.turnNum ∨ ch.state = ss.state) ∧ net.chain.now + T.ε ≤ ch.deadline)) (Ω : Outcome E) (hen : Enabled apps T c Ω net) : Ω = Ω1 ∨ Ω = Ω2
```

#### `turbo_redistribution_unbeatable`

D1, D-E, new gap G15. `Assumptions` becomes `Bounds` plus `Threat.CapableTransfers`; `TransfersOnly` excludes ticks (Nitro:779-781 'transfer operations only'); the strategy uses transfers only (`CanObtainIn … HonestMove.IsTransfer`). The target is an external destination: a finalized channel target can pay its coins onward in the same round.

Old (`aa52443`):

```lean
theorem turbo_redistribution_unbeatable(apps : Apps) {p : Participant} (T : Threat p) (A : Assumptions apps p T) (hT : T.TransfersOnly) (net : NetworkState p) (hdag : net.chain.IsDAG) (ops : List (Participant × Op)) (hops : OnlyTransfers ops) (a : Address) (x : Coins) (hgoal : x ≤ (Adjudicator.applyAll apps ops net.chain).balances.get a) : CanObtain apps T a x net
```

New:

```lean
theorem turbo_redistribution_unbeatable(apps : Apps E) {p : Participant} (T : Threat E p) (B : Bounds apps p T) (hT : T.TransfersOnly) (hcap : T.CapableTransfers) (net : NetworkState E p) (hdag : net.chain.IsDAG) (ops : List (Participant × Op E)) (hops : OnlyTransfers ops) (d : E) (x : Coins) (hgoal : x ≤ (Adjudicator.applyAll apps ops net.chain).balances.get (.external d)) : CanObtainIn apps T HonestMove.IsTransfer (.external d) x net
```

#### `deposit_bounds_value`

D-E. `Value` takes the external destination `d` (operator ruling: destinations are not participants).

Old (`aa52443`):

```lean
theorem deposit_bounds_value(apps : Apps) {p : Participant} (T : Threat p) (A : Assumptions apps p T) (net : NetworkState p) (c : FixedPart) (y x x' : Coins) (s' : Adjudicator) (e : Coins) (hd : net.chain.deposit c.address e y = some s') (hv : Value apps T net x) (hv' : Value apps T { net with chain := s' } x') : x ≤ x' ∧ x' ≤ x + y
```

New:

```lean
theorem deposit_bounds_value(apps : Apps E) {p : Participant} (T : Threat E p) (A : Assumptions apps p T) (net : NetworkState E p) (c : FixedPart) (d : E) (y x x' : Coins) (s' : Adjudicator E) (e : Coins) (hd : net.chain.deposit c.address e y = some s') (hv : Value apps T d net x) (hv' : Value apps T d { net with chain := s' } x') : x ≤ x' ∧ x' ≤ x + y
```

#### `payout_to_other_affects_only_owner`

D-E. `q` and `d` are external destinations; `hq : q ≠ d`.

Old (`aa52443`):

```lean
theorem payout_to_other_affects_only_owner(apps : Apps) {p : Participant} (T : Threat p) (A : Assumptions apps p T) (net : NetworkState p) (q : Participant) (hq : q ≠ p) (a : FixedPart) (s' : Adjudicator) (h : net.chain.transfer a (.participant q) = some s') (x : Coins) : Value apps T net x ↔ Value apps T { net with chain := s' } x
```

New:

```lean
theorem payout_to_other_affects_only_owner(apps : Apps E) {p : Participant} (T : Threat E p) (A : Assumptions apps p T) (net : NetworkState E p) (d q : E) (hq : q ≠ d) (a : FixedPart) (s' : Adjudicator E) (h : net.chain.transfer a (.external q) = some s') (x : Coins) : Value apps T d net x ↔ Value apps T d { net with chain := s' } x
```

#### `participant_can_prevent_cycles`

D-E, G8. New `hopen`: every channel of `p` is open. The goal speaks of cycles through channels of `p` (Nitro:792-794 'any participant in the channel').

Old (`aa52443`):

```lean
theorem participant_can_prevent_cycles(apps : Apps) {p : Participant} (T : Threat p) (A : Assumptions apps p T) (net : NetworkState p) (hc : ∀ c : FixedPart, p ∈ c.participants → apps c.appDef = consensusRules) (hdag : net.chain.IsDAG) (hsent : net.sent = []) : Prevents apps T (fun net' => ¬ net'.chain.IsDAG) net
```

New:

```lean
theorem participant_can_prevent_cycles(apps : Apps E) {p : Participant} (T : Threat E p) (A : Assumptions apps p T) (net : NetworkState E p) (hc : ∀ c : FixedPart, p ∈ c.participants → apps c.appDef = consensusRules) (hopen : ∀ c : FixedPart, p ∈ c.participants → ∃ t, net.chain.statusOf c = .open t) (hdag : net.chain.IsDAG) (hsent : net.sent = []) : Prevents apps T (fun net' => ∃ c : FixedPart, p ∈ c.participants ∧ Relation.TransGen net'.chain.Edge c.address c.address) net
```

#### `turbo_value_upper_bound`

D1, D-E. As `turbo_redistribution_unbeatable`: `Bounds`, `CapableTransfers`, the transfer-only game.

Old (`aa52443`):

```lean
theorem turbo_value_upper_bound(apps : Apps) {p : Participant} (T : Threat p) (A : Assumptions apps p T) (hT : T.TransfersOnly) (net : NetworkState p) (hdag : net.chain.IsDAG) (n : Address) (v x : Coins) (hv : net.chain.TurboValue n v) (h : CanObtain apps T n x net) : x ≤ v
```

New:

```lean
theorem turbo_value_upper_bound(apps : Apps E) {p : Participant} (T : Threat E p) (B : Bounds apps p T) (hT : T.TransfersOnly) (hcap : T.CapableTransfers) (net : NetworkState E p) (hdag : net.chain.IsDAG) (n : Address E) (v x : Coins) (hv : net.chain.TurboValue n v) (h : CanObtainIn apps T HonestMove.IsTransfer n x net) : x ≤ v
```

#### `turbo_value_achievable`

D1, D-E, G15. As `turbo_redistribution_unbeatable`, for an external destination.

Old (`aa52443`):

```lean
theorem turbo_value_achievable(apps : Apps) {p : Participant} (T : Threat p) (A : Assumptions apps p T) (hT : T.TransfersOnly) (net : NetworkState p) (hdag : net.chain.IsDAG) (n : Address) (v : Coins) (hv : net.chain.TurboValue n v) : CanObtain apps T n v net
```

New:

```lean
theorem turbo_value_achievable(apps : Apps E) {p : Participant} (T : Threat E p) (B : Bounds apps p T) (hT : T.TransfersOnly) (hcap : T.CapableTransfers) (net : NetworkState E p) (hdag : net.chain.IsDAG) (d : E) (v : Coins) (hv : net.chain.TurboValue (.external d) v) : CanObtainIn apps T HonestMove.IsTransfer (.external d) v net
```

#### `turbo_value_is_value`

D1, D-E. `ValueIn … HonestMove.IsTransfer d`, for the external destination `d`.

Old (`aa52443`):

```lean
theorem turbo_value_is_value(apps : Apps) {p : Participant} (T : Threat p) (A : Assumptions apps p T) (hT : T.TransfersOnly) (net : NetworkState p) (hdag : net.chain.IsDAG) (v : Coins) (hv : net.chain.TurboValue p.address v) : Value apps T net v
```

New:

```lean
theorem turbo_value_is_value(apps : Apps E) {p : Participant} (T : Threat E p) (B : Bounds apps p T) (hT : T.TransfersOnly) (hcap : T.CapableTransfers) (net : NetworkState E p) (hdag : net.chain.IsDAG) (d : E) (v : Coins) (hv : net.chain.TurboValue (.external d) v) : ValueIn apps T HonestMove.IsTransfer d net v
```

#### `subchannel_open_value_preserving`

D-E. `dA`, `dB` are the destinations of `A`, `B`; `SameValue` takes the destination.

Old (`aa52443`):

```lean
theorem subchannel_open_value_preserving(apps : Apps) (Ts : Threats apps) (v v' : Views) (hv : v.Consistent) (hv' : v'.Consistent) (A B : Participant) (L χ : FixedPart) (a b a' b' : Coins) (ha : a' ≤ a) (hb : b' ≤ b) (hL : IsLedgerChannel apps L) (hLp : L.participants = [A, B]) (hχp : χ.participants = [A, B]) (hbal : v.HoldsBalance L.address (a + b)) (hbal' : v'.HoldsBalance L.address (a + b)) (h1 : v.FinalizableBy apps Ts L (.allocation [alloc A.address a, alloc B.address b]) [A, B]) (h2 : v.FinalizableBy apps Ts χ (.allocation [alloc A.address a', alloc B.address b']) [A, B]) (h3 : v'.FinalizableBy apps Ts L (.allocation [alloc A.address (a - a'), alloc B.address (b - b'), alloc χ.address (a' + b')]) [A, B]) (h4 : v'.FinalizableBy apps Ts χ (.allocation [alloc A.address a', alloc B.address b']) [A, B]) (hother : ∀ p, p = A ∨ p = B → (v p).chain = (v' p).chain) : SameValue apps (Ts.T A) (v A) (v' A) ∧ SameValue apps (Ts.T B) (v B) (v' B)
```

New:

```lean
theorem subchannel_open_value_preserving(apps : Apps E) (Ts : Threats E apps) (v v' : Views E) (hv : v.Consistent) (hv' : v'.Consistent) (A B : Participant) (dA dB : E) (L χ : FixedPart) (a b a' b' : Coins) (ha : a' ≤ a) (hb : b' ≤ b) (hL : IsLedgerChannel apps L) (hLp : L.participants = [A, B]) (hχp : χ.participants = [A, B]) (hbal : v.HoldsBalance L.address (a + b)) (hbal' : v'.HoldsBalance L.address (a + b)) (h1 : v.FinalizableBy apps Ts L (.allocation [alloc (.external dA) a, alloc (.external dB) b]) [A, B]) (h2 : v.FinalizableBy apps Ts χ (.allocation [alloc (.external dA) a', alloc (.external dB) b']) [A, B]) (h3 : v'.FinalizableBy apps Ts L (.allocation [alloc (.external dA) (a - a'), alloc (.external dB) (b - b'), alloc χ.address (a' + b')]) [A, B]) (h4 : v'.FinalizableBy apps Ts χ (.allocation [alloc (.external dA) a', alloc (.external dB) b']) [A, B]) (hother : ∀ p, p = A ∨ p = B → (v p).chain = (v' p).chain) : SameValue apps (Ts.T A) dA (v A) (v' A) ∧ SameValue apps (Ts.T B) dB (v B) (v' B)
```

#### `subchannel_close_value_preserving`

D-E. `w.dA`, `w.dB` (new fields of `LedgerWithSub`); `SameValue` takes the destination.

Old (`aa52443`):

```lean
theorem subchannel_close_value_preserving(apps : Apps) (Ts : Threats apps) (v v' : Views) (hv : v.Consistent) (hv' : v'.Consistent) (w : LedgerWithSub) (a' b' : Coins) (hc : a' + b' = w.c) (hw : w.Holds apps Ts v) (hχ : v.FinalizableBy apps Ts w.χ (.allocation [alloc w.A.address a', alloc w.B.address b']) [w.A, w.B]) (h3 : v'.FinalizableBy apps Ts w.L (.allocation [alloc w.A.address (w.a + a'), alloc w.B.address (w.b + b')]) [w.A, w.B]) (hbal' : v'.HoldsBalance w.L.address (w.a + w.b + w.c)) (hother : ∀ p, p = w.A ∨ p = w.B → (v p).chain = (v' p).chain) : SameValue apps (Ts.T w.A) (v w.A) (v' w.A) ∧ SameValue apps (Ts.T w.B) (v w.B) (v' w.B)
```

New:

```lean
theorem subchannel_close_value_preserving(apps : Apps E) (Ts : Threats E apps) (v v' : Views E) (hv : v.Consistent) (hv' : v'.Consistent) (w : LedgerWithSub E) (a' b' : Coins) (hc : a' + b' = w.c) (hw : w.Holds apps Ts v) (hχ : v.FinalizableBy apps Ts w.χ (.allocation [alloc (.external w.dA) a', alloc (.external w.dB) b']) [w.A, w.B]) (h3 : v'.FinalizableBy apps Ts w.L (.allocation [alloc (.external w.dA) (w.a + a'), alloc (.external w.dB) (w.b + b')]) [w.A, w.B]) (hbal' : v'.HoldsBalance w.L.address (w.a + w.b + w.c)) (hother : ∀ p, p = w.A ∨ p = w.B → (v p).chain = (v' p).chain) : SameValue apps (Ts.T w.A) w.dA (v w.A) (v' w.A) ∧ SameValue apps (Ts.T w.B) w.dB (v w.B) (v' w.B)
```

#### `ledger_partial_withdrawal`

D-E, D6, clock, new gap G16. `dA`, `dB` destinations. `hopen` reads the outcome of finalization. New `hdur`, `hpend` for `L` and `L'`, `hL'open` and `hL'sent`: `L'` cannot finalize (and pay its coins onward) before `L` pays it.

Old (`aa52443`):

```lean
theorem ledger_partial_withdrawal(apps : Apps) (Ts : Threats apps) (v : Views) (hv : v.Consistent) (A B : Participant) (L L' χ : FixedPart) (a b c a' : Coins) (hL : IsLedgerChannel apps L) (hL' : IsLedgerChannel apps L') (hLp : L.participants = [A, B]) (hL'p : L'.participants = [A, B]) (hLL' : L ≠ L') (hbal : v.HoldsBalance L.address (a + b + c + a')) (hconc : Concluded v L (.allocation [alloc L'.address (a + b + c), alloc A.address a'])) (hsent : ∀ p, ∀ t ∈ (v p).sent, t.state.channel = L → t.state.isFinal = true → t.state.outcome = .allocation [alloc L'.address (a + b + c), alloc A.address a']) (hopen : ∀ p, (v p).chain.finalOutcome L.address = none) (hL'out : v.FinalizableBy apps Ts L' (.allocation [alloc A.address a, alloc B.address b, alloc χ.address c]) [A, B]) : UnbeatableNoWait apps (Ts.T A) (fun net' => (v A).chain.balances.get A.address + a' ≤ net'.chain.balances.get A.address) (v A) ∧ FundedFor apps (Ts.T A) L' (a + b + c) (v A) ∧ FundedFor apps (Ts.T B) L' (a + b + c) (v B)
```

New:

```lean
theorem ledger_partial_withdrawal(apps : Apps E) (Ts : Threats E apps) (v : Views E) (hv : v.Consistent) (A B : Participant) (dA dB : E) (L L' χ : FixedPart) (a b c a' : Coins) (hL : IsLedgerChannel apps L) (hL' : IsLedgerChannel apps L') (hLp : L.participants = [A, B]) (hL'p : L'.participants = [A, B]) (hLL' : L ≠ L') (hbal : v.HoldsBalance L.address (a + b + c + a')) (hconc : Concluded v L (.allocation [alloc L'.address (a + b + c), alloc (.external dA) a'])) (hsent : ∀ p, ∀ t ∈ (v p).sent, t.state.channel = L → t.state.isFinal = true → t.state.outcome = .allocation [alloc L'.address (a + b + c), alloc (.external dA) a']) (hopen : ∀ p, (v p).chain.finalizedWith L.address = none) (hdur : ∀ p, 2 * (Ts.T p).ε ≤ L.challengeDuration ∧ 2 * (Ts.T p).ε ≤ L'.challengeDuration) (hpend : ∀ p, (v p).DeadlineAfter L (Ts.T p).ε ∧ (v p).DeadlineAfter L' (2 * (Ts.T p).ε)) (hL'open : ∀ p, (v p).chain.finalOutcome L'.address = none) (hL'sent : ∀ p, ∀ t ∈ (v p).sent, t.state.channel = L' → t.state.isFinal = false) (hL'out : v.FinalizableBy apps Ts L' (.allocation [alloc (.external dA) a, alloc (.external dB) b, alloc χ.address c]) [A, B]) : UnbeatableNoWait apps (Ts.T A) (fun net' => (v A).chain.balances.get (.external dA) + a' ≤ net'.chain.balances.get (.external dA)) (v A) ∧ FundedFor apps (Ts.T A) L' (a + b + c) (v A) ∧ FundedFor apps (Ts.T B) L' (a + b + c) (v B)
```

#### `satp_outcome_change_keeps_total`

D-E. With external destinations the voucher outcome pays the start state's first two destinations (`Outcome.pairDests`), so the second conjunct names them instead of `PairOutcome alice bob`.

Old (`aa52443`):

```lean
theorem satp_outcome_change_keeps_total(c : FixedPart) (alice bob : Participant) (proof : SupportProof) (candidate : State) (h : validateOutcomeChange c alice bob proof candidate = true) (s0 : SignedState) (h0 : proof.head? = some s0) : candidate.outcome.fundedTotal = s0.state.outcome.fundedTotal ∧ (candidate ≠ s0.state → ∃ a b, PairOutcome alice bob candidate.outcome a b ∧ a + b = s0.state.outcome.fundedTotal)
```

New:

```lean
theorem satp_outcome_change_keeps_total(c : FixedPart) (alice bob : Participant) (proof : SupportProof E) (candidate : State E) (h : validateOutcomeChange c alice bob proof candidate = true) (s0 : SignedState E) (h0 : proof.head? = some s0) : candidate.outcome.fundedTotal = s0.state.outcome.fundedTotal ∧ (candidate ≠ s0.state → ∃ da db a b, s0.state.outcome.pairDests = some (da, db) ∧ candidate.outcome = .allocation [⟨da, .alloc a⟩, ⟨db, .alloc b⟩] ∧ a + b = s0.state.outcome.fundedTotal)
```

#### `satp_lemma_3_1`

D2, D-E. `hsetup` and `hfinal` quantified over every `SignedState` value (false for every route). They become `signed` (the signatures that exist), `hsigned` (every state all peers signed is a setup state with the original outcome or a final pair with the total), and `hs : ReachableSigned apps signed s`. Destinations are `r.dest alice`, `r.dest bob`.

Old (`aa52443`):

```lean
theorem satp_lemma_3_1(apps : Apps) (r : Route) (alice bob : Participant) (hr : r.WellFormed apps) (hV : apps r.V.appDef = satpVirtualRules) (halice : r.peers.head? = some alice) (hbob : r.peers.getLast? = some bob) (hsetup : ∀ ss : SignedState, ss.ByAll → ss.state.channel = r.V → ss.state.turnNum ≤ 1 → ss.state.outcome = originalOutcome alice bob r.a0 r.b0) (hfinal : ∀ ss : SignedState, ss.ByAll → ss.state.channel = r.V → ss.state.isFinal = true → ∃ a b, PairOutcome alice bob ss.state.outcome a b ∧ a + b = r.a0 + r.b0) (s : Adjudicator) (hs : Reachable apps s) (Ω : Outcome) (hfin : s.finalOutcome r.V.address = some Ω) : ∃ Ω0, Redistributed Ω0 Ω ∧ (((s.statusOf r.V).turnNumRecord = 0 ∧ Ω0 = originalOutcome alice bob r.a0 r.b0) ∨ (∃ a b, PairOutcome alice bob Ω0 a b ∧ a + b = r.a0 + r.b0))
```

New:

```lean
theorem satp_lemma_3_1(apps : Apps E) (r : Route E) (alice bob : Participant) (hr : r.WellFormed apps) (hV : apps r.V.appDef = satpVirtualRules) (halice : r.peers.head? = some alice) (hbob : r.peers.getLast? = some bob) (signed : List (Participant × State E)) (hsigned : ∀ st : State E, (∀ q ∈ r.V.participants, (q, st) ∈ signed) → st.channel = r.V → (st.turnNum ≤ 1 ∧ st.outcome = originalOutcome (r.dest alice) (r.dest bob) r.a0 r.b0) ∨ (st.isFinal = true ∧ ∃ a b, PairOutcome (r.dest alice) (r.dest bob) st.outcome a b ∧ a + b = r.a0 + r.b0)) (s : Adjudicator E) (hs : ReachableSigned apps signed s) (Ω : Outcome E) (hfin : s.finalOutcome r.V.address = some Ω) : ∃ Ω0, Redistributed Ω0 Ω ∧ (((s.statusOf r.V).turnNumRecord = 0 ∧ Ω0 = originalOutcome (r.dest alice) (r.dest bob) r.a0 r.b0) ∨ (∃ a b, PairOutcome (r.dest alice) (r.dest bob) Ω0 a b ∧ a + b = r.a0 + r.b0))
```

#### `satp_peers_can_finalize`

D-E, G1, G10, clock. `hsent`: each signed state of `V` is a setup state with the original outcome or a pair outcome with the total (`fundedTotal` read only the first two amounts). `hchain` becomes `hst`: `V` is open at version 1 or below. `hdur` is `2 * ε`.

Old (`aa52443`):

```lean
theorem satp_peers_can_finalize(apps : Apps) {p : Participant} (T : Threat p) (A : Assumptions apps p T) (r : Route) (alice bob : Participant) (hr : r.WellFormed apps) (hV : apps r.V.appDef = satpVirtualRules) (hp : p ∈ r.peers) (halice : r.peers.head? = some alice) (hbob : r.peers.getLast? = some bob) (hdur : 0 < r.V.challengeDuration) (net : NetworkState p) (s1 : SignedState) (hh : net.Holds s1) (hall : s1.ByAll) (hchan : s1.state.channel = r.V) (hv1 : s1.state.turnNum = 1) (h1 : s1.state.outcome = originalOutcome alice bob r.a0 r.b0) (hsent : ∀ t ∈ net.sent, t.state.channel = r.V → t.state.outcome.fundedTotal = r.a0 + r.b0) (hchain : net.chain.finalOutcome r.V.address = none) : Unbeatable apps T (fun net' => ∃ Ω a b, net'.Finalized r.V Ω ∧ PairOutcome alice bob Ω a b ∧ a + b = r.a0 + r.b0) net
```

New:

```lean
theorem satp_peers_can_finalize(apps : Apps E) {p : Participant} (T : Threat E p) (A : Assumptions apps p T) (r : Route E) (alice bob : Participant) (hr : r.WellFormed apps) (hV : apps r.V.appDef = satpVirtualRules) (hp : p ∈ r.peers) (halice : r.peers.head? = some alice) (hbob : r.peers.getLast? = some bob) (hdur : 2 * T.ε ≤ r.V.challengeDuration) (net : NetworkState E p) (s1 : SignedState E) (hh : net.Holds s1) (hall : s1.ByAll) (hchan : s1.state.channel = r.V) (hv1 : s1.state.turnNum = 1) (h1 : s1.state.outcome = originalOutcome (r.dest alice) (r.dest bob) r.a0 r.b0) (hsent : ∀ t ∈ net.sent, t.state.channel = r.V → (t.state.turnNum ≤ 1 ∧ t.state.outcome = originalOutcome (r.dest alice) (r.dest bob) r.a0 r.b0) ∨ (∃ a b, PairOutcome (r.dest alice) (r.dest bob) t.state.outcome a b ∧ a + b = r.a0 + r.b0)) (hst : ∃ t, net.chain.statusOf r.V = .open t ∧ t ≤ 1) : Unbeatable apps T (fun net' => ∃ Ω a b, net'.Finalized r.V Ω ∧ PairOutcome (r.dest alice) (r.dest bob) Ω a b ∧ a + b = r.a0 + r.b0) net
```

#### `satp_theorem_3_2`

D2, D-E, G1, G2, G6/G7, new gap G14b. `hsetup` is dropped: `P`'s own signatures on `V` are `HoldsVirtualSetup`, and `Bounds.unforgeable` bounds the rest. `HoldsLatestLedger` now also forbids signed final ledger states and constrains the chain record (definition change). New `hpend`; `hchain` reads the outcome of finalization; `hdur` is `2 * ε`. `LedgerAfterRound2` names the debited peer (`om Pprev P P`): the old `om Pprev P` debited `Pprev`, while the goal reads `P`'s entry (SATP:436-439: in `L_i` the left peer pays `a0`, the right peer `b0`). The goal `IntermediaryRecovered` reads the stored outcomes (after reclaim) and counts `P`'s destination balance above `base`, so a payout does not undo it.

Old (`aa52443`):

```lean
theorem satp_theorem_3_2(apps : Apps) {P : Participant} (T : Threat P) (A : Assumptions apps P T) (r : Route) (alice bob : Participant) (hr : r.WellFormed apps) (hV : apps r.V.appDef = satpVirtualRules) (halice : r.peers.head? = some alice) (hbob : r.peers.getLast? = some bob) (i : Nat) (hi : 1 ≤ i) (hin : i + 1 < r.peers.length) (hP : r.peers[i]? = some P) (Pprev Pnext : Participant) (hprev : r.peers[i - 1]? = some Pprev) (hnext : r.peers[i + 1]? = some Pnext) (Lm Lp : FixedPart) (hLm : r.ledgers[i - 1]? = some Lm) (hLp : r.ledgers[i]? = some Lp) (hdur : 0 < Lm.challengeDuration ∧ 0 < Lp.challengeDuration ∧ 0 < r.V.challengeDuration) (om op : Allocation) (balm balp : Coins) (hom : r.LedgerAfterRound2 om Pprev P balm r.b0) (hop : r.LedgerAfterRound2 op P Pnext balp r.a0) (net : NetworkState P) (hHm : HoldsLatestLedger net Lm om) (hHp : HoldsLatestLedger net Lp op) (hVs : HoldsVirtualSetup net r alice bob true) (hsetup : ∀ ss : SignedState, ss.ByAll → ss.state.channel = r.V → ss.state.turnNum ≤ 1 → ss.state.outcome = originalOutcome alice bob r.a0 r.b0) (hchain : net.chain.finalOutcome Lm.address = none ∧ net.chain.finalOutcome Lp.address = none ∧ net.chain.finalOutcome r.V.address = none) : Unbeatable apps T (IntermediaryRecovered r Lm Lp balm balp) net
```

New:

```lean
theorem satp_theorem_3_2(apps : Apps E) {P : Participant} (T : Threat E P) (A : Assumptions apps P T) (r : Route E) (alice bob : Participant) (hr : r.WellFormed apps) (hV : apps r.V.appDef = satpVirtualRules) (halice : r.peers.head? = some alice) (hbob : r.peers.getLast? = some bob) (i : Nat) (hi : 1 ≤ i) (hin : i + 1 < r.peers.length) (hP : r.peers[i]? = some P) (Pprev Pnext : Participant) (hprev : r.peers[i - 1]? = some Pprev) (hnext : r.peers[i + 1]? = some Pnext) (Lm Lp : FixedPart) (hLm : r.ledgers[i - 1]? = some Lm) (hLp : r.ledgers[i]? = some Lp) (hdur : 2 * T.ε ≤ Lm.challengeDuration ∧ 2 * T.ε ≤ Lp.challengeDuration ∧ 2 * T.ε ≤ r.V.challengeDuration) (om op : Allocation E) (balm balp : Coins) (hom : r.LedgerAfterRound2 om Pprev P P balm r.b0) (hop : r.LedgerAfterRound2 op P Pnext P balp r.a0) (net : NetworkState E P) (hHm : HoldsLatestLedger net Lm om) (hHp : HoldsLatestLedger net Lp op) (hVs : HoldsVirtualSetup net r alice bob true) (hpend : net.DeadlineAfter Lm T.ε ∧ net.DeadlineAfter Lp T.ε ∧ net.DeadlineAfter r.V T.ε) (hchain : net.chain.finalizedWith Lm.address = none ∧ net.chain.finalizedWith Lp.address = none ∧ net.chain.finalizedWith r.V.address = none) : Unbeatable apps T (IntermediaryRecovered r Lm Lp balm balp (net.chain.balances.get (.external (r.dest P)))) net
```

#### `satp_intermediary_before_round2`

D-E, G1, G2, clock. As `satp_theorem_3_2`: `HoldsLatestLedger` (definition change), new `hpend`, `hchain` on the outcome of finalization, `hdur`, and the goal with `base`.

Old (`aa52443`):

```lean
theorem satp_intermediary_before_round2(apps : Apps) {P : Participant} (T : Threat P) (A : Assumptions apps P T) (r : Route) (hr : r.WellFormed apps) (i : Nat) (hi : 1 ≤ i) (hin : i + 1 < r.peers.length) (hP : r.peers[i]? = some P) (Lm Lp : FixedPart) (hLm : r.ledgers[i - 1]? = some Lm) (hLp : r.ledgers[i]? = some Lp) (hdur : 0 < Lm.challengeDuration ∧ 0 < Lp.challengeDuration) (om op : Allocation) (balm balp : Coins) (hom : r.LedgerBeforeRound2 om P balm) (hop : r.LedgerBeforeRound2 op P balp) (net : NetworkState P) (hHm : HoldsLatestLedger net Lm om) (hHp : HoldsLatestLedger net Lp op) (hchain : net.chain.finalOutcome Lm.address = none ∧ net.chain.finalOutcome Lp.address = none) : Unbeatable apps T (IntermediaryRecovered r Lm Lp balm balp) net
```

New:

```lean
theorem satp_intermediary_before_round2(apps : Apps E) {P : Participant} (T : Threat E P) (A : Assumptions apps P T) (r : Route E) (hr : r.WellFormed apps) (i : Nat) (hi : 1 ≤ i) (hin : i + 1 < r.peers.length) (hP : r.peers[i]? = some P) (Lm Lp : FixedPart) (hLm : r.ledgers[i - 1]? = some Lm) (hLp : r.ledgers[i]? = some Lp) (hdur : 2 * T.ε ≤ Lm.challengeDuration ∧ 2 * T.ε ≤ Lp.challengeDuration) (om op : Allocation E) (balm balp : Coins) (hom : r.LedgerBeforeRound2 om P balm) (hop : r.LedgerBeforeRound2 op P balp) (net : NetworkState E P) (hHm : HoldsLatestLedger net Lm om) (hHp : HoldsLatestLedger net Lp op) (hpend : net.DeadlineAfter Lm T.ε ∧ net.DeadlineAfter Lp T.ε) (hchain : net.chain.finalizedWith Lm.address = none ∧ net.chain.finalizedWith Lp.address = none) : Unbeatable apps T (IntermediaryRecovered r Lm Lp balm balp (net.chain.balances.get (.external (r.dest P)))) net
```

#### `satp_end_user_recovers`

D-E, G6, clock. New `hab : a + b = r.a0 + r.b0` (go-nitro reclaim needs it, MultiAssetHolder.sol:365). `hfin` reads the stored outcome of `V` (reclaim reads it). `HoldsLatestLedger` forbids a signed final state of `L0` (the suspicion of the first audit). New `hpend`; `hdur` is `2 * ε`; the debited peer is named; the goal counts the balance above `base`.

Old (`aa52443`):

```lean
theorem satp_end_user_recovers(apps : Apps) {P : Participant} (T : Threat P) (A : Assumptions apps P T) (r : Route) (alice bob : Participant) (hr : r.WellFormed apps) (hV : apps r.V.appDef = satpVirtualRules) (halice : r.peers.head? = some alice) (hbob : r.peers.getLast? = some bob) (hPA : P = alice) (P1 : Participant) (hP1 : r.peers[1]? = some P1) (L0 : FixedPart) (hL0 : r.ledgers[0]? = some L0) (hdur : 0 < L0.challengeDuration ∧ 0 < r.V.challengeDuration) (o : Allocation) (bal : Coins) (ho : r.LedgerAfterRound2 o P P1 bal r.a0) (net : NetworkState P) (hH : HoldsLatestLedger net L0 o) (hVs : HoldsVirtualSetup net r alice bob true) (a b : Coins) (hfin : net.Finalized r.V (.allocation [alloc alice.address a, alloc bob.address b])) (hchain : net.chain.finalOutcome L0.address = none) : Unbeatable apps T (EndUserRecovered r L0 bal a) net
```

New:

```lean
theorem satp_end_user_recovers(apps : Apps E) {P : Participant} (T : Threat E P) (A : Assumptions apps P T) (r : Route E) (alice bob : Participant) (hr : r.WellFormed apps) (hV : apps r.V.appDef = satpVirtualRules) (halice : r.peers.head? = some alice) (hbob : r.peers.getLast? = some bob) (hPA : P = alice) (P1 : Participant) (hP1 : r.peers[1]? = some P1) (L0 : FixedPart) (hL0 : r.ledgers[0]? = some L0) (hdur : 2 * T.ε ≤ L0.challengeDuration ∧ 2 * T.ε ≤ r.V.challengeDuration) (o : Allocation E) (bal : Coins) (ho : r.LedgerAfterRound2 o P P1 P bal r.a0) (net : NetworkState E P) (hH : HoldsLatestLedger net L0 o) (hVs : HoldsVirtualSetup net r alice bob true) (a b : Coins) (hab : a + b = r.a0 + r.b0) (hfin : net.chain.finalOutcome r.V.address = some (.allocation [alloc (.external (r.dest alice)) a, alloc (.external (r.dest bob)) b])) (hpend : net.DeadlineAfter L0 T.ε) (hchain : net.chain.finalizedWith L0.address = none) : Unbeatable apps T (EndUserRecovered r L0 bal a (net.chain.balances.get (.external (r.dest P)))) net
```

#### `satp_reclaim_credits_intermediary`

D-E. Peers' destinations are `r.dest P` etc.; `hdist` compares destinations.

Old (`aa52443`):

```lean
theorem satp_reclaim_credits_intermediary(s : Adjudicator) (r : Route) (alice bob P Pprev Pnext : Participant) (Lm Lp : FixedPart) (om op : Allocation) (a b : Coins) (hdist : P ≠ Pprev ∧ P ≠ Pnext ∧ Pprev ≠ Pnext) (hV : s.finalOutcome r.V.address = some (.allocation [alloc alice.address a, alloc bob.address b])) (hLm : s.finalOutcome Lm.address = some (.allocation om)) (hLp : s.finalOutcome Lp.address = some (.allocation op)) (hgm : om.find r.V.address = some (r.guarantee Pprev P)) (hgp : op.find r.V.address = some (r.guarantee P Pnext)) (hne : Lm ≠ Lp) (hem : om.find Pprev.address ≠ none ∧ om.find P.address ≠ none) (hep : op.find P.address ≠ none ∧ op.find Pnext.address ≠ none) (hab : a + b = r.a0 + r.b0) : ∃ s1 s2 om' op', s.reclaim Lm r.V = some s1 ∧ s1.reclaim Lp r.V = some s2 ∧ s2.finalOutcome Lm.address = some (.allocation om') ∧ s2.finalOutcome Lp.address = some (.allocation op') ∧ om'.owed P.address = om.owed P.address + b ∧ op'.owed P.address = op.owed P.address + a ∧ om'.find r.V.address = none ∧ op'.find r.V.address = none
```

New:

```lean
theorem satp_reclaim_credits_intermediary(s : Adjudicator E) (r : Route E) (alice bob P Pprev Pnext : Participant) (Lm Lp : FixedPart) (om op : Allocation E) (a b : Coins) (hdist : r.dest P ≠ r.dest Pprev ∧ r.dest P ≠ r.dest Pnext ∧ r.dest Pprev ≠ r.dest Pnext) (hV : s.finalOutcome r.V.address = some (.allocation [alloc (.external (r.dest alice)) a, alloc (.external (r.dest bob)) b])) (hLm : s.finalOutcome Lm.address = some (.allocation om)) (hLp : s.finalOutcome Lp.address = some (.allocation op)) (hgm : om.find r.V.address = some (r.guarantee Pprev P)) (hgp : op.find r.V.address = some (r.guarantee P Pnext)) (hne : Lm ≠ Lp) (hem : om.find (.external (r.dest Pprev)) ≠ none ∧ om.find (.external (r.dest P)) ≠ none) (hep : op.find (.external (r.dest P)) ≠ none ∧ op.find (.external (r.dest Pnext)) ≠ none) (hab : a + b = r.a0 + r.b0) : ∃ s1 s2 om' op', s.reclaim Lm r.V = some s1 ∧ s1.reclaim Lp r.V = some s2 ∧ s2.finalOutcome Lm.address = some (.allocation om') ∧ s2.finalOutcome Lp.address = some (.allocation op') ∧ om'.owed (.external (r.dest P)) = om.owed (.external (r.dest P)) + b ∧ op'.owed (.external (r.dest P)) = op.owed (.external (r.dest P)) + a ∧ om'.find r.V.address = none ∧ op'.find r.V.address = none
```

## 5. Acceptance evidence

Run in the worktree at the commit of this file:

- `~/.elan/bin/lake build`: exit 0; 31 `declaration uses 'sorry'` warnings, all in `Liveness.lean`.
- `#print axioms` on the 63 theorems of `Safety.lean` (58 approved theorems and 5 helper theorems), on the 4
  proved Liveness theorems and on the strategy lemmas of `NonVacuity.lean`: each lists a subset of `propext`,
  `Classical.choice`, `Quot.sound`, or no axiom. No `sorryAx`.
- `grep -c "^example" ArmadaLean/Nitro/NonVacuity.lean` is 88: the 63 theorems of `Safety.lean` minus the 10
  with no hypotheses beyond their binders' types (listed in the module comment of `NonVacuity.lean`), plus the
  35 theorems of `Liveness.lean`. The module builds with no `sorry`.
- No `axiom` in `ArmadaLean/Nitro/`.

## 6. Second revision, 2026-10-27: channel types, D9, G16, `finalizable_is_enabled` removed

Four changes, approved by the operator and the coordinator on 2026-10-27, on top of the repair above.

### 6.1 `finalizable_is_enabled` removed

Coordinator ruling, replacing the brief's item 5 ("leave `finalizable_is_enabled` unchanged"). Nitro 2019 §4.4
(Nitro:641-658) defines the enabled outcomes as those `p` has no strategy to prevent, and states that exactly
one of "`p` has at least one finalizable outcome" and "`p` has at least two enabled outcomes" holds
(`finalizable_or_two_enabled`, `single_enabled_is_finalizable`). It never claims finalizable implies enabled;
the dichotomy rules it out when a channel has a unique finalizable outcome. `docs/nitro-theorems.md` now maps
Nitro-21 and Nitro-24 to `finalizable_or_two_enabled` and `single_enabled_is_finalizable` only. The theorem
and its `NonVacuity.lean` witness are deleted; no other declaration referenced it.

### 6.2 D9: a successful on-chain operation adds its proof states to every participant's received states

The defect (§3 above): an adversary that registers a challenge or a checkpoint and never delivers it gains a
move the honest participant cannot answer, because `p` can use a state only if it is in `sent` or `received`.
`NetworkState.applyAdv` (`Strategy.lean`) now adds `op.proofStates` to `received` when the chain call succeeds,
matching go-nitro: a challenge emits `ChallengeRegistered` with the signed states, and a checkpoint call's
calldata is public. A definition change; no theorem's type changed. The four proved `Liveness.lean` theorems do
not mention `NetworkState` or `applyAdv` and are unaffected.

### 6.3 Channel types by construction (operator ruling 2026-10-27, SATP §1 SATP:79-84, SATP §3.1)

SATP §1 (SATP:79-84): "ledger channels, which are typically funded by the underlying ledger, and virtual
channels, which are funded by ledger channels." A ledger channel is funded by deposits or by an allocation in
another channel's outcome. A virtual channel is funded only by guarantees held in two or more ledger channels,
holding no assets of its own. `FixedPart` (`Address.lean`) gets a field `kind : ChannelKind` (`ledger` or
`virtual`), fixed at construction: the on-chain channel id is an untyped hash of the fixed part (SATP:213,
Nitro:158-160), so the type is an addition the specification states, not an encoding of anything the chain
already enforces. `Adjudicator.deposit` and `Adjudicator.transfer` (`Adjudicator.lean`) now succeed only for a
ledger channel; `transfer`'s paid destination, when it names a channel, must be a ledger channel too
(`Address.fundable`). `Adjudicator.reclaim` succeeds only when its ledger is a `ledger` channel and its target
is virtual, matching "a guarantee may target only a virtual channel." `Route.WellFormed` (`SATP.lean`) requires
`kind = .ledger` for each ledger and `.virtual` for `V`.

`Adjudicator.reclaim` also now reads the target's outcome of finalization, `finalizedWith` (SATP §2.4
SATP:335-338: "x tokens to be reclaimed, using the 'finalized' outcome of V"), not its current stored outcome.
go-nitro reads the current stored outcome, and `transfer` can rewrite it between finalization and a later
`reclaim` call: the reclaim denial-of-service reproduced against go-nitro at `64c4ee9a1`
(`armada-laconic/labbook/2026-10-27-gonitro-reclaim-dos.md`) deposits into a finalized virtual channel, pays
the deposit out by `transfer`, and every later `reclaim` then reverts forever on the amount check
(`totalReclaimed != guarantee.amount`, `MultiAssetHolder.sol:365`). With channel types a virtual channel
accepts neither a deposit nor a transfer, so its stored outcome cannot move once finalized; reading
`finalizedWith` states that fact directly, as SATP reads it, instead of leaving it to follow only from the
deposit and transfer guards.

Coordinator ruling 2026-10-27: the channel-kind constructor for a ledger channel is renamed to
`ChannelKind.ledger`, to use SATP's own term (SATP:79-84) in place of an English compound the brief had coined.
Every reference in `ArmadaLean/Nitro/` and `docs/` changed with it.

Operator ruling 2026-10-27: the three `Safety.lean` theorems first added for this repair,
`transfer_pays_at_most_held`, `reclaim_moves_guarantee_amount` and `virtual_finalized_outcome_immutable`, are
removed, with their `NonVacuity.lean` witnesses: they are not paper theorems. `transfer_pays_at_most_held` is
redundant with `transfer_effects` and `payout_bounded`; `reclaim_moves_guarantee_amount` is redundant with
`reclaim_effects` (the credits and `oL'.total = oL.total`). `virtual_finalized_outcome_immutable` is replaced
by `Adjudicator.finalizedWith_stable` in `Lemmas.lean`, the same statement without the unused channel-kind
hypothesis (the fact holds for every channel kind): a proof helper, not a `Safety.lean` theorem, with no
`NonVacuity.lean` witness of its own.

#### `deposit_can_happen`

New hypothesis `c.kind = .ledger`: the theorem claimed every channel accepts a deposit, which is no longer true
of a virtual one.

Old (`568b6fd`):

```lean
theorem deposit_can_happen (apps : Apps E) (caller : Participant) (s : Adjudicator E) (c : FixedPart) (x : Coins) : s.apply apps caller (.deposit c.address (s.balances.get c.address) x) = some { s with balances := s.balances.add c.address x, held := s.held + x }
```

New:

```lean
theorem deposit_can_happen (apps : Apps E) (caller : Participant) (s : Adjudicator E) (c : FixedPart) (hk : c.kind = .ledger) (x : Coins) : s.apply apps caller (.deposit c.address (s.balances.get c.address) x) = some { s with balances := s.balances.add c.address x, held := s.held + x }
```

#### `deposits_in_order_succeed`

New hypothesis `c.kind = .ledger`, passed to `deposit_can_happen`.

Old (`568b6fd`):

```lean
theorem deposits_in_order_succeed (apps : Apps E) (s : Adjudicator E) (c : FixedPart) (o : Allocation E) (callers : List Participant) (h0 : s.balances.get c.address = 0) : let op := …
```

New:

```lean
theorem deposits_in_order_succeed (apps : Apps E) (s : Adjudicator E) (c : FixedPart) (o : Allocation E) (callers : List Participant) (hck : c.kind = .ledger) (h0 : s.balances.get c.address = 0) : let op := …
```

#### `transfer_can_happen`

New hypotheses `a.kind = .ledger` and `b.fundable = true`.

Old (`568b6fd`):

```lean
theorem transfer_can_happen (s : Adjudicator E) (a : FixedPart) (b : Address E) (o : Allocation E) (amt : Coins) (hf : s.finalOutcome a.address = some (.allocation o)) (hb : o.find b = some ⟨b, .alloc amt⟩) : ∃ s', s.transfer a b = some s' ∧ s'.balances.get b = s.balances.get b + (if b = a.address then 0 else o.paidTo (s.balances.get a.address) b)
```

New:

```lean
theorem transfer_can_happen (s : Adjudicator E) (a : FixedPart) (b : Address E) (o : Allocation E) (amt : Coins) (ha : a.kind = .ledger) (hbf : b.fundable = true) (hf : s.finalOutcome a.address = some (.allocation o)) (hb : o.find b = some ⟨b, .alloc amt⟩) : ∃ s', s.transfer a b = some s' ∧ s'.balances.get b = s.balances.get b + (if b = a.address then 0 else o.paidTo (s.balances.get a.address) b)
```

#### `reclaim_requires`

New conjuncts `l.kind = .ledger ∧ v.kind = .virtual` in the conclusion; `v`'s outcome is read as
`finalizedWith` (SATP §2.4), not `finalOutcome`.

Old (`568b6fd`):

```lean
theorem reclaim_requires (s : Adjudicator E) (l v : FixedPart) (s' : Adjudicator E) (h : s.reclaim l v = some s') : s.mode l = .finalized ∧ s.mode v = .finalized ∧ ∃ oL oV x left right, s.finalOutcome l.address = some (.allocation oL) ∧ s.finalOutcome v.address = some (.allocation oV) ∧ oL.find v.address = some ⟨v.address, .guarantee x [left, right]⟩ ∧ (oL.remove v.address).find left ≠ none ∧ (oL.remove v.address).find right ≠ none ∧ oV.amountAt 0 + oV.amountAt 1 = x
```

New:

```lean
theorem reclaim_requires (s : Adjudicator E) (l v : FixedPart) (s' : Adjudicator E) (h : s.reclaim l v = some s') : s.mode l = .finalized ∧ s.mode v = .finalized ∧ l.kind = .ledger ∧ v.kind = .virtual ∧ ∃ oL oV x left right, s.finalOutcome l.address = some (.allocation oL) ∧ s.finalizedWith v.address = some (.allocation oV) ∧ oL.find v.address = some ⟨v.address, .guarantee x [left, right]⟩ ∧ (oL.remove v.address).find left ≠ none ∧ (oL.remove v.address).find right ≠ none ∧ oV.amountAt 0 + oV.amountAt 1 = x
```

#### `reclaim_effects`, `reclaim_can_happen`, `reclaim_fails_without_entries`

`hV` reads `v`'s outcome as `finalizedWith`, not `finalOutcome`. `reclaim_can_happen` also takes two new
hypotheses `l.kind = .ledger` and `v.kind = .virtual`.

Old `hV` (all three, `568b6fd`): `(hV : s.finalOutcome v.address = some (.allocation oV))`.

New `hV` (all three): `(hV : s.finalizedWith v.address = some (.allocation oV))`.

`reclaim_can_happen` old (`568b6fd`):

```lean
theorem reclaim_can_happen (s : Adjudicator E) (l v : FixedPart) (oL oV : Allocation E) (x : Coins) (left right : Address E) (hL : s.finalOutcome l.address = some (.allocation oL)) (hV : s.finalOutcome v.address = some (.allocation oV)) (hg : oL.find v.address = some ⟨v.address, .guarantee x [left, right]⟩) (hl : (oL.remove v.address).find left ≠ none) (hr : (oL.remove v.address).find right ≠ none) (hx : oV.amountAt 0 + oV.amountAt 1 = x) : s.reclaim l v = some (s.setStatus l ((s.statusOf l).withOutcome (.allocation ((((oL.addTo left (oV.amountAt 0)).addTo right (oV.amountAt 1))).remove v.address))))
```

New:

```lean
theorem reclaim_can_happen (s : Adjudicator E) (l v : FixedPart) (oL oV : Allocation E) (x : Coins) (left right : Address E) (hkl : l.kind = .ledger) (hkv : v.kind = .virtual) (hL : s.finalOutcome l.address = some (.allocation oL)) (hV : s.finalizedWith v.address = some (.allocation oV)) (hg : oL.find v.address = some ⟨v.address, .guarantee x [left, right]⟩) (hl : (oL.remove v.address).find left ≠ none) (hr : (oL.remove v.address).find right ≠ none) (hx : oV.amountAt 0 + oV.amountAt 1 = x) : s.reclaim l v = some (s.setStatus l ((s.statusOf l).withOutcome (.allocation ((((oL.addTo left (oV.amountAt 0)).addTo right (oV.amountAt 1))).remove v.address))))
```

#### `ledger_offload_funds_subchannel`

G16 (defect 23 in §3 above, applied here as the brief required): `w.χ` must not finalize during the strategy,
the hypothesis `ledger_partial_withdrawal` already carries for its receiving ledger.

Old (`568b6fd`):

```lean
theorem ledger_offload_funds_subchannel (apps : Apps E) (Ts : Threats E apps) (v : Views E) (hv : v.Consistent) (w : LedgerWithSub E) (hw : w.Holds apps Ts v) : FundedFor apps (Ts.T w.A) w.χ w.c (v w.A) ∧ FundedFor apps (Ts.T w.B) w.χ w.c (v w.B)
```

New:

```lean
theorem ledger_offload_funds_subchannel (apps : Apps E) (Ts : Threats E apps) (v : Views E) (hv : v.Consistent) (w : LedgerWithSub E) (hw : w.Holds apps Ts v) (hχopen : ∀ p, (v p).chain.finalOutcome w.χ.address = none) (hχsent : ∀ p, ∀ t ∈ (v p).sent, t.state.channel = w.χ → t.state.isFinal = false) : FundedFor apps (Ts.T w.A) w.χ w.c (v w.A) ∧ FundedFor apps (Ts.T w.B) w.χ w.c (v w.B)
```

#### `satp_reclaim_credits_intermediary` (one of the four proved Liveness theorems; stays proved)

New hypotheses `Lm.kind = .ledger`, `Lp.kind = .ledger`, `r.V.kind = .virtual`; `hV` reads `V`'s outcome as
`finalizedWith`. The new proof derives `Lm ≠ V` and `Lp ≠ V` directly from the kind mismatch
(`rw [hkV] at hkLm; cases hkLm`), replacing the old argument through the guarantee's outcome structure.

Old (`568b6fd`):

```lean
theorem satp_reclaim_credits_intermediary (s : Adjudicator E) (r : Route E) (alice bob P Pprev Pnext : Participant) (Lm Lp : FixedPart) (om op : Allocation E) (a b : Coins) (hdist : r.dest P ≠ r.dest Pprev ∧ r.dest P ≠ r.dest Pnext ∧ r.dest Pprev ≠ r.dest Pnext) (hV : s.finalOutcome r.V.address = some (.allocation [alloc (.external (r.dest alice)) a, alloc (.external (r.dest bob)) b])) (hLm : s.finalOutcome Lm.address = some (.allocation om)) (hLp : s.finalOutcome Lp.address = some (.allocation op)) (hgm : om.find r.V.address = some (r.guarantee Pprev P)) (hgp : op.find r.V.address = some (r.guarantee P Pnext)) (hne : Lm ≠ Lp) (hem : om.find (.external (r.dest Pprev)) ≠ none ∧ om.find (.external (r.dest P)) ≠ none) (hep : op.find (.external (r.dest P)) ≠ none ∧ op.find (.external (r.dest Pnext)) ≠ none) (hab : a + b = r.a0 + r.b0) : ∃ s1 s2 om' op', …
```

New:

```lean
theorem satp_reclaim_credits_intermediary (s : Adjudicator E) (r : Route E) (alice bob P Pprev Pnext : Participant) (Lm Lp : FixedPart) (om op : Allocation E) (a b : Coins) (hdist : r.dest P ≠ r.dest Pprev ∧ r.dest P ≠ r.dest Pnext ∧ r.dest Pprev ≠ r.dest Pnext) (hkLm : Lm.kind = .ledger) (hkLp : Lp.kind = .ledger) (hkV : r.V.kind = .virtual) (hV : s.finalizedWith r.V.address = some (.allocation [alloc (.external (r.dest alice)) a, alloc (.external (r.dest bob)) b])) (hLm : s.finalOutcome Lm.address = some (.allocation om)) (hLp : s.finalOutcome Lp.address = some (.allocation op)) (hgm : om.find r.V.address = some (r.guarantee Pprev P)) (hgp : op.find r.V.address = some (r.guarantee P Pnext)) (hne : Lm ≠ Lp) (hem : om.find (.external (r.dest Pprev)) ≠ none ∧ om.find (.external (r.dest P)) ≠ none) (hep : op.find (.external (r.dest P)) ≠ none ∧ op.find (.external (r.dest Pnext)) ≠ none) (hab : a + b = r.a0 + r.b0) : ∃ s1 s2 om' op', …
```

### 6.4 Acceptance evidence for the second revision

- `~/.elan/bin/lake build`: exit 0; 30 `declaration uses 'sorry'` warnings, all in `Liveness.lean` (34
  theorems, 4 proved).
- `#print axioms` on the 63 theorems of `Safety.lean` and the 4 proved `Liveness.lean` theorems: each lists a
  subset of `propext`, `Classical.choice`, `Quot.sound`. No `sorryAx`.
- `grep -c "^example" ArmadaLean/Nitro/NonVacuity.lean` is 88: 63 `Safety.lean` theorems minus the 9 listed as
  having no hypotheses, plus the 34 theorems of `Liveness.lean`. The module builds with no `sorry`.
- No `axiom` in `ArmadaLean/Nitro/`.
- A search of `ArmadaLean/Nitro/` and `docs/` for the renamed constructor's earlier spelling, concatenated,
  hyphenated or spaced, finds nothing.
