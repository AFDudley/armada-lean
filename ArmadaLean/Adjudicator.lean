/-
  ArmadaLean.Adjudicator — the armada-nitro adjudicator model, phase 1
  stage A (state, operations, the three assumptions, theorem statements).

  Read in this order:
  - `Outcome.lean`      — allocations, guarantees, the priority payout rule.
  - `Assumptions.lean`  — hash and signature axioms (assumptions 1, 2).
  - `Channel.lean`      — channel state, support, modes, finalizability.
  - `Notes.lean`        — the Armada layer: pool notes, the owned-spend
                           circuit, proof soundness (assumption 3).
  - `State.lean`        — the full adjudicator state and `heldValue`.
  - `Operations.lean`   — every call and its effect.
  - `Reachability.lean` — every state any sequence of calls can reach.
  - `Safety.lean`       — the theorem statements, proofs `sorry`.

  See `Safety.lean`'s module comment for the three questions this model
  answers and the sources it answers them from.

  ## Sources

  Every comment in these files cites a source by its tag below. The local
  copies are in armada-nitro at commit
  `55939ef87d9ce8ecc1e5a8912b495031aa71531e`, directory
  `docs/references/nitro/sources/`
  (https://github.com/AFDudley/armada-nitro/tree/55939ef87d9ce8ecc1e5a8912b495031aa71531e/docs/references/nitro/sources).
  The testable clauses taken from them, numbered as the comments cite them
  ("clause N"), are in `docs/references/nitro/clauses.md` at the same commit.

  - S1. Tom Close, Andrew Stewart, "ForceMove: an n-party state channel
    protocol", 2018-11-20. https://magmo.com/force-move-games.pdf
    Copy: `forcemove-2018.pdf`, sha256
    a546ba7c76ea039cfafa81e4c5840eec9fde456187f0de759344ec11598df407.
    Used for: definitions (the final state divides the assets; a dispute
    resolves by the most recent known state).
  - S2. Tom Close, "Nitro Protocol", IACR ePrint 2019/219, 2019-02-24.
    https://eprint.iacr.org/2019/219 (same bytes as
    https://magmo.com/nitro-protocol.pdf). Copy: `nitro-2019-219.pdf`,
    sha256 4330ffb53d713721f84a53200519af7f92f3254306e81acae0d5fc2e616fb04b.
    Used for: definitions (finalizable and enabled outcomes, §4.4; the
    priority payout rule, §5.1).
  - S3. Andrew Stewart, Colin Kennedy, Mike Kerzhner, George Knee, Matthias
    Geihs, Sebastian Stammler, "SATP: A simple and scalable protocol for
    virtual state channel networks", 2022-09-28.
    https://statechannels.github.io/satp_paper/satp.pdf (404 on 2026-10-18;
    copy taken from web.archive.org). Copy: `satp-2022.pdf`, sha256
    7a5faa2ebe44dfb884d3a90d9e3e9b3a33f7291b4841a51a1b4333476cfb64d5.
    Used for: current mechanics, and the safety and liveness premises.
  - S4. docs.statechannels.org, protocol tutorial pages 0010-0080 and
    research-papers, retrieved 2026-10-18. https://docs.statechannels.org/
    Copies: `docs.statechannels.org/*.html`. Used for: current mechanics
    (states, support, outcomes, lifecycle, funding, finalizing, defunding).

  S1 and S2 are older than S3 and S4 in their mechanics (for example,
  turn-taking now lives in the app). The model takes definitions from S1 and
  S2 and mechanics from S3 and S4. Comments mark each place where they do not
  fit together.

  The vendored upstream contracts that implement S3 and S4 are armada-nitro
  `src/nitro/*.sol`. Armada's own sources (the N1a-N3 briefs,
  `R1-adjudicator-rewrite.md`, the lab book §3a and §5, the `TransactOwned`
  circuit, the pool contracts) are cited by path where they are used.
-/
import ArmadaLean.Adjudicator.Outcome
import ArmadaLean.Adjudicator.Assumptions
import ArmadaLean.Adjudicator.Channel
import ArmadaLean.Adjudicator.Notes
import ArmadaLean.Adjudicator.State
import ArmadaLean.Adjudicator.Operations
import ArmadaLean.Adjudicator.Reachability
import ArmadaLean.Adjudicator.Safety
