# The Nitro model's scope

This module (`ArmadaLean/Nitro/`, the Nitro-dependent files under
`ArmadaLean/Types/`, `ArmadaLean/Spec/Nitro/`, `ArmadaLean/Witness/Nitro/`,
and `docs/counterexamples/`) states and proves properties of the Nitro,
ForceMove, and SATP papers and of go-nitro, the reference implementation
those papers describe. It does not model any Armada contract. A reader
checks each claim below against the cited declaration before relying on it.

## The G17 fix is a model addition, not a go-nitro property

`satp_theorem_3_2` and `satp_end_user_recovers` do not hold for go-nitro as
deployed. They hold for this model, which adds a field go-nitro's on-chain
state does not have.

The G17 defect (`docs/nitro-repair-2026-10-27.md` §3, "Reclaim griefing"):
go-nitro's `reclaim` call checks that the virtual channel's stored outcome
still sums to the funded amount (`MultiAssetHolder.sol:365`). Any account
can deposit into a finalized virtual channel and call `transfer` out of it.
`transfer` rewrites the stored outcome (`_updateFingerprint`), the sum check
then fails, and every later `reclaim` call reverts. An intermediary or an
end user who is owed a reclaim can be denied it forever by one adversary
transaction. The defect is reproduced against go-nitro `64c4ee9a1` and
recorded in `docs/nitro-repair-2026-10-27.md` §3.

The fix in this model is a type, not a go-nitro change: `ChannelKind`
(`ArmadaLean/Nitro/Address.lean`), a field of `FixedPart` with two values,
`ledger` and `virtual`. Go-nitro and the SATP paper have no such field; they
encode the ledger/virtual distinction only in which operations happen to
succeed. With `ChannelKind`, `Adjudicator.deposit` and `Adjudicator.transfer`
succeed only on a ledger channel, and `Adjudicator.reclaim` reads the
target's `finalizedWith` outcome instead of its mutable stored outcome
(`ArmadaLean/Nitro/Adjudicator.lean`). The finalized outcome cannot change
after finalization, unlike the mutable stored outcome `transfer` rewrites. This
closes G17 inside the model. Go-nitro's own `MultiAssetHolder.sol` is
unchanged by this model and still has the defect.

So `satp_theorem_3_2` (an honest intermediary recovers its ledger balances,
SATP Theorem 3.2, `ArmadaLean/Nitro/Liveness.lean`) and
`satp_end_user_recovers` (the end-user analogue of Theorem 3.2,
`ArmadaLean/Nitro/Liveness.lean`) are proved against the model with
`ChannelKind`. Neither theorem is a claim about go-nitro as deployed. A
reader who wants a go-nitro guarantee needs the G17 fix shipped in go-nitro
first; until then, an honest intermediary's or end user's reclaim can be
griefed exactly as `docs/nitro-repair-2026-10-27.md` §3 reproduces.

## The signer rules are obligations on the wallet, not on the chain

`Types/Honest.lean` (`HonestSend`) states six rules for what an honest
participant signs. The Nitro and SATP liveness theorems assume every
reachable signed state obeys these rules
(`Nitro.participant_sent_honest`, `ArmadaLean/Nitro/Reachable.lean`). The
chain enforces none of them; a signature the chain accepts can violate any
one of the six. An Armada client that signs Nitro/ForceMove states (a
wallet) must enforce all six itself, or the liveness theorems do not apply
to that wallet's channels:

1. **`noConflict`.** Below a channel's funding point, never sign two states
   of that channel at one slot with two different outcomes (one slot is one
   setup turn, with every setup turn merged into one slot for this rule).
2. **`guaranteesExternal`.** Every guarantee entry a signed outcome creates
   names only external destinations, never another channel.
3. **`fundsCommitted`.** Before signing a SATP Round 2 ledger state, confirm
   the Round 1 state it is built on is committed (SATP Definition 3.1).
4. **`movesFrom`.** Above the funding point, sign a new state only as a
   ForceMove-valid move from a state already held, at the turn before.
5. **`oneState`.** Sign at most one state per turn number of a channel.
   Re-signing the identical state is allowed.
6. **`finalLast`.** After signing a final state of a channel, sign only
   final states of that channel.

A wallet that violates any rule is an honest participant's own-violation: the
theorems' conclusions no longer apply to that wallet's channels, with no
chain-level signal that the violation occurred.

## The Nitro-24 restatement is close to a tautology

`docs/nitro-theorems.md`'s Nitro-24 claim appears as two statements in
`ArmadaLean/Nitro/TakeOut.lean`: `finalizable_or_two_enabled` ("a participant
has a finalizable outcome or two enabled outcomes") and
`single_enabled_is_finalizable` ("a single enabled outcome is finalizable").
Each is a one-line case split on the other, not an independent result: given
one exists, if more than one outcome is enabled the first disjunct of
`finalizable_or_two_enabled` is immediate, and if exactly one is enabled it
must be the finalizable one.

Both are corollaries of one proof, `exit_finalizes`
(`ArmadaLean/Nitro/TakeOut.lean`). `exit_finalizes` is the real content: from
every reachable state where `p` holds a support of a channel at a turn no
lower than the turn the chain records (`ExitReady`), and a running challenge
on that channel ends no sooner than `ε` from now, the exit strategy
(`exitStrategy`) is unbeatable for the goal of finalizing that channel. Both
Nitro-24 theorems call `exit_finalizes` directly and derive their conclusion
from its `.sound` result (lines 820 and 844 of `TakeOut.lean`). A reader who
wants the substance of Nitro-24 should read `exit_finalizes` and `ExitReady`,
not the two restatements.
