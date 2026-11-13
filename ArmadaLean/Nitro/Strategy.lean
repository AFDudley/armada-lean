/-
  Nitro protocol specification: network states, strategies, unbeatable
  strategies, finalizable and enabled outcomes, funding and value. Source:
  Nitro §4 (lines 359-709); SATP:164-168 gives the two security assumptions
  and SATP:393-399 the commit step. go-nitro has no off-chain model. See
  `Address.lean` for the source list. The repair of 2026-10-27 is recorded in
  `docs/nitro-repair-2026-10-27.md`.

  Modelling choice (the game). Nitro:460-461: "we assume that all other
  participants are controlled by a single adversary, pooling their resources
  and commitments." The honest participant `p` plays against that adversary.
  One round is: `p` issues a reaction (`Reaction`, possibly several on-chain
  calls and sends), the adversary plays a feasible sequence of its own moves
  and lands every call of that reaction, in whatever order it chooses
  (front-running, Nitro:540-542), then the round ends. The clock follows
  Nitro:537-539: "Transactions are unimpeded: given that the current time is
  t and ε > 0, then it is possible for any party to apply any operation, O,
  on-chain before time t + ε."

  Time bounds per pending action: "Time
  bounds per pending action". The earlier game bounded the adversary's
  clock advance per honest MOVE: a strategy needing two on-chain calls spent
  two rounds, and the second call could land almost `2 * ε` after the round
  started. Lamport's explicit-time form fixes this:
  each call `p` issues at time `t` is pending with deadline `t + ε`
  (`Reaction`, `Threat.RoundSeq.land`); the clock's `tick` is disabled while
  it would pass a pending deadline, an enabling condition on `Tick`
  (Lamport, "Real-Time Model Checking is Really Simple", CHARME 2005: "An
  upper-bound timing constraint on when an action A must occur is expressed
  by an enabling condition on the Tick action"; the same explicit-time
  encoding is Abadi and Lamport, "An Old-Fashioned Recipe for Real Time",
  TOPLAS 1994, and the per-task upper bound is Merritt, Modugno and Tuttle's
  `boundmap`, 1991 — time-constrained automata, MIT 6.852 lecture 25; the
  on-chain round that bounds every published response while the adversary
  reorders and front-runs is the Sprites payment-channel network, arXiv
  1702.05812v2 §I, `∆`). A reaction's calls still land one at a time, each
  wherever the adversary orders it among its own moves, so two calls issued
  together (SATP Protocol 3.3 and Theorem 3.1, SATP:480-493, challenge both
  ledgers of an intermediary together) share one deadline, not two
  (`satp_intermediary_before_round2`'s argument, `Liveness.lean`). The old
  per-move bound (one call, `net'.chain.now < net.chain.now + T.ε`,
  evaluated once the round ends) is the special case of one call
  (`Threat.Round.single`, below).
-/
import ArmadaLean.Nitro.Adjudicator
import ArmadaLean.Nitro.Lemmas
import ArmadaLean.Types.Honest
import Mathlib.Tactic.Says

namespace ArmadaLean.Nitro

variable {E : Type} [DecidableEq E]

/-- Nitro:446-454: "The network state, Σ, for a participant, A, consists of:
    1. The state of the adjudicator ... 2. For each channel A is a participant
    of: (a) Signed commitments that A has received (b) Signed commitments that
    A has sent (c) Private information held by A". The private information is
    the signing key; it is implicit in `p`. -/
structure NetworkState (E : Type) (p : Participant) where
  chain : Adjudicator E
  received : List (SignedState E)
  sent : List (SignedState E)

/-- The signed states `p` can assemble. Every signer is `p` on a state `p`
    sent, or a participant whose signature `p` received on that state. Every
    signer listed in the state's voucher (SATP:703) is `p` on a voucher `p`
    sent, or a received state that carries the voucher (its
    signatures travel inside the voucher, SATP:630-637; see
    the funding-point alternative-moves analysis). -/
def NetworkState.Holds {p : Participant} (net : NetworkState E p) (ss : SignedState E) : Prop :=
  (∀ q ∈ ss.signers,
    (q = p ∧ ∃ s ∈ net.sent, s.state = ss.state) ∨
    (∃ r ∈ net.received, r.state = ss.state ∧ q ∈ r.signers)) ∧
  ∀ v, ss.state.voucher? = some v → ∀ q ∈ v.signers,
    (q = p ∧ ∃ s ∈ net.sent, s.state.voucher? = some v) ∨
    (∃ r ∈ net.received, r.state.voucher? = some v)

omit [DecidableEq E] in
/-- `Holds` survives a larger `sent` and a larger `received`: each disjunct
    names one member of one of the two lists. -/
theorem NetworkState.Holds.of_subset {p : Participant} {net net' : NetworkState E p}
    {ss : SignedState E} (hsent : ∀ s ∈ net.sent, s ∈ net'.sent)
    (hrecv : ∀ r ∈ net.received, r ∈ net'.received) (h : net.Holds ss) : net'.Holds ss := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨fun q hq => ?_, fun v hv q hq => ?_⟩
  · rcases h1 q hq with ⟨hqp, s, hs, heq⟩ | ⟨r, hr, heq, hqr⟩
    · exact .inl ⟨hqp, s, hsent s hs, heq⟩
    · exact .inr ⟨r, hrecv r hr, heq, hqr⟩
  · rcases h2 v hv q hq with ⟨hqp, s, hs, heq⟩ | ⟨r, hr, heq⟩
    · exact .inl ⟨hqp, s, hsent s hs, heq⟩
    · exact .inr ⟨r, hrecv r hr, heq⟩

/-- `p` holds the all-signed pre-fund (turn 0) state of `V`: SATP:409,
    "Proceed when s0 is committed" (Definition 3.1, SATP:394-399). The held
    pre-fund states of `HonestSend.fundsCommitted` (`Types/Honest.lean`). -/
def NetworkState.HoldsPrefund {p : Participant} (net : NetworkState E p) (V : FixedPart) : Prop :=
  ∃ ss, net.Holds ss ∧ ss.ByAll ∧ ss.state.channel = V ∧ ss.state.turnNum = 0

/-- One honest reaction (Nitro:485-488: "signing commitments, refusing to
    sign commitments, launching/responding to on-chain challenges and
    calling on-chain operations"): the on-chain calls `p` submits and the
    states `p` signs and sends, issued together at one time `t`. Each call
    in `calls` becomes pending with deadline `t + ε` (`Threat.RoundSeq.land`);
    `sends` carry no deadline, SATP:393-399's commit step, and take effect
    at once (`NetworkState.applyHonest`). A strategy may put calls to two
    different channels in one reaction (SATP Protocol 3.3). -/
structure Reaction (E : Type) where
  calls : List (Op E)
  sends : List (State E)

/-- A move of the honest participant: issue a reaction, or let the clock
    advance unilaterally. `wait` is `p`'s own choice, not subject to the
    adversary's `Tick` enabling condition below, which bounds only the
    adversary's own clock advances against `p`'s pending calls. -/
inductive HonestMove (E : Type)
  | react (r : Reaction E)
  | wait (dt : Time)

/-- A move of the adversary: an on-chain operation by some other participant,
    a signed state delivered to `p`, the clock moving, or landing one of
    `p`'s own pending calls (front-running: Nitro:540-542, "Transactions can
    be front-run"; the adversary chooses where `land` falls among its own
    moves). `land`'s caller is always `p`: it is `p`'s own already-issued
    call reaching the chain, not a forgery, so it needs no `Bounds`
    hypothesis (`Threat.RoundSeq.land` below gates it structurally instead:
    only a call `p` actually issued, every other listed as still pending). -/
inductive AdvMove (E : Type)
  | chain (caller : Participant) (op : Op E)
  | deliver (ss : SignedState E)
  | tick (dt : Time)
  | land (op : Op E)

/-- `op`'s own feasibility as one call of a reaction: `p` does not deposit
    (Nitro:779-781 analyses strategies "ignoring deposits and withdrawals",
    and `p` has no wallet, so a deposit by `p` would create coins), `p`
    does not submit `.tick` as a call (time advances only through `p`'s own
    `HonestMove.wait` or the adversary's `Tick`, never as a pending call to
    land — landing a `.tick` would force the clock past its own deadline
    just to land it, making `Threat.Round` unsatisfiable for that reaction
    and every goal vacuously "unbeatable"; soundness finding, this design decision's
    own review), and every proof state `op` submits is one `p` holds. -/
def Op.HonestFeasible {p : Participant} (net : NetworkState E p) : Op E → Prop
  | .deposit .. => False
  | .tick .. => False
  | op => ∀ ss ∈ op.proofStates, net.Holds ss

/-- A feasible call's own feasibility, unfolded to its one non-trivial
    shape (`deposit`/`tick` cannot be feasible calls). -/
theorem Op.HonestFeasible.mem {p : Participant} {net : NetworkState E p} {op : Op E}
    (h : op.HonestFeasible net) : ∀ ss ∈ op.proofStates, net.Holds ss := by
  cases op with
  | deposit a e x => exact absurd h (by (simp? [Op.HonestFeasible] says simp only [HonestFeasible, not_false_eq_true]))
  | tick dt => exact absurd h (by (simp? [Op.HonestFeasible] says simp only [HonestFeasible, not_false_eq_true]))
  | transfer a b => exact h
  | reclaim l v => exact h
  | challenge c proof cand => exact h
  | checkpoint c proof cand => exact h
  | conclude c ss => exact h

/-- A reaction is feasible when every one of its calls is. -/
def Reaction.Feasible {p : Participant} (net : NetworkState E p) (r : Reaction E) : Prop :=
  ∀ op ∈ r.calls, op.HonestFeasible net

/-- `p` holds a support of a state of `c` at turn `k`: every state of the
    support proof is held, and the app of `c` supports the candidate. -/
def NetworkState.HoldsSupportAt {p : Participant} (apps : Apps E) (net : NetworkState E p)
    (c : FixedPart) (k : Nat) : Prop :=
  ∃ proof cand, (∀ ss ∈ proof, net.Holds ss) ∧ (apps c.appDef).supports c proof cand = true ∧
    cand.channel = c ∧ cand.turnNum = k

/-- `p` can move to `st` by the rules: `p` holds a support of a state of
    the channel of `st` at the turn before, and `p`'s held states with `st`
    support `st` (a valid move from the current state, ForceMove:744-778).
    The argument `canMove` of `HonestSend` (`HonestSend.movesFrom`). -/
def NetworkState.CanMoveTo {p : Participant} (apps : Apps E) (net : NetworkState E p)
    (st : State E) : Prop :=
  net.HoldsSupportAt apps st.channel (st.turnNum - 1) ∧
  ∃ proof', (∀ ss ∈ proof', net.Holds ss ∨ ss.state = st) ∧
    (apps st.channel.appDef).supports st.channel proof' st = true

omit [DecidableEq E] in
/-- The held pre-fund states and the possible moves survive any change that
    keeps every held state held (for example `NetworkState.Holds.of_subset`). -/
theorem NetworkState.held_mono {p : Participant} {apps : Apps E} {net net' : NetworkState E p}
    (hmono : ∀ ss, net.Holds ss → net'.Holds ss) :
    (∀ V, net.HoldsPrefund V → net'.HoldsPrefund V) ∧
      ∀ st, net.CanMoveTo apps st → net'.CanMoveTo apps st :=
  ⟨fun _ ⟨ss, hH, hall, hc, ht⟩ => ⟨ss, hmono ss hH, hall, hc, ht⟩,
    fun _ ⟨⟨proof, cand, hH, hs, hc, hk⟩, proof', hH', hs'⟩ =>
      ⟨⟨proof, cand, fun ss hss => hmono ss (hH ss hss), hs, hc, hk⟩, proof',
        fun ss hss => (hH' ss hss).imp_left (hmono ss), hs'⟩⟩

/-- Every send of `r` satisfies the signing rules (`HonestSend`,
    `Types/Honest.lean`): against every state `p` has signed once `r`'s sends
    are out (`NetworkState.applyHonest`'s `.react` arm), and against the
    pre-fund states and the supports `p` holds now. -/
def Reaction.SendsHonest {p : Participant} (apps : Apps E) (net : NetworkState E p)
    (r : Reaction E) : Prop :=
  ∀ st ∈ r.sends,
    HonestSend (r.sends.map (fun st => (⟨st, [p]⟩ : SignedState E)) ++ net.sent) net.HoldsPrefund
      (net.CanMoveTo apps) st

/-- The honest participant may play a reaction only when every one of its
    calls is feasible and every one of its sends satisfies the signing rules
    (`Reaction.SendsHonest`, `Types/Honest.lean`:
    the honest strategy makes a signed state only here). `wait` is always
    feasible. -/
def HonestMove.Feasible {p : Participant} (apps : Apps E) (net : NetworkState E p) :
    HonestMove E → Prop
  | .react r => r.Feasible net ∧ r.SendsHonest apps net
  | .wait _ => True

/-- A move whose calls are feasible, with no rule on its sends: the honest
    step of the unrestricted machines (`Nitro.participantUnrestricted`,
    `Nitro.networkUnrestricted`, `Reachable.lean`), whose counterexamples need
    a participant that signs against the rules of `HonestSend`. -/
def HonestMove.CallsFeasible {p : Participant} (net : NetworkState E p) : HonestMove E → Prop
  | .react r => r.Feasible net
  | .wait _ => True

/-- A feasible move's calls are feasible. -/
theorem HonestMove.Feasible.callsFeasible {p : Participant} {apps : Apps E}
    {net : NetworkState E p} {m : HonestMove E} (h : m.Feasible apps net) : m.CallsFeasible net := by
  cases m with
  | react r => exact h.1
  | wait dt => trivial

/-- Apply an honest move, once its round has landed every call (`Threat.Round`
    below runs the round first; this only ever touches `sent`/`chain` for
    the parts of a move that are NOT a pending call — a reaction's calls are
    already reflected in the chain by the time this runs, through
    `Threat.RoundSeq.land`). `wait` still moves the clock directly: it is
    `p`'s own move, not the adversary's gated `Tick`. -/
def NetworkState.applyHonest {p : Participant} (m : HonestMove E) (net : NetworkState E p) :
    NetworkState E p :=
  match m with
  | .react r => { net with sent := r.sends.map (fun st => (⟨st, [p]⟩ : SignedState E)) ++ net.sent }
  | .wait dt => { net with chain := net.chain.tick dt }

/-- Apply an adversary move. D9 repair (`docs/nitro-repair-2026-10-27.md`):
    go-nitro emits the signed states of a challenge (`ChallengeRegistered`)
    and a checkpoint is calldata, so every on-chain call makes its proof
    states public. A successful chain operation (`.chain`, by another
    participant, or `.land`, `p`'s own pending call landing) adds
    `op.proofStates` to `received`: the honest participant can then answer a
    challenge or checkpoint it did not see delivered, closing the gap that
    let the adversary register an undeliverable state (theorems
    `funding_point_universally_finalizable`, `satp_peers_can_finalize`,
    `satp_theorem_3_2` in the re-audit). -/
def NetworkState.applyAdv (apps : Apps E) {p : Participant}
    (m : AdvMove E) (net : NetworkState E p) : NetworkState E p :=
  match m with
  | .chain caller op =>
    match net.chain.apply apps caller op with
    | some s' => { net with chain := s', received := op.proofStates ++ net.received }
    | none => net
  | .deliver ss => { net with received := ss :: net.received }
  | .tick dt => { net with chain := net.chain.tick dt }
  | .land op =>
    match net.chain.apply apps p op with
    | some s' => { net with chain := s', received := op.proofStates ++ net.received }
    | none => net

/-! `applyAdv` reading lemmas (`writing-lean.md` rule 3). -/

/-- `applyAdv` of an on-chain call that succeeds (`writing-lean.md` rule 3). -/
@[simp] theorem NetworkState.applyAdv_chain_some (apps : Apps E) {p : Participant}
    {net : NetworkState E p} {caller : Participant} {op : Op E} {s' : Adjudicator E}
    (h : net.chain.apply apps caller op = some s') :
    net.applyAdv apps (.chain caller op) = { net with chain := s', received := op.proofStates ++ net.received } := by
  (simp? [NetworkState.applyAdv, h] says simp only [applyAdv, h])

/-- `applyAdv` of an on that fails: nothing changes. -/
@[simp] theorem NetworkState.applyAdv_chain_none (apps : Apps E) {p : Participant}
    {net : NetworkState E p} {caller : Participant} {op : Op E}
    (h : net.chain.apply apps caller op = none) :
    net.applyAdv apps (.chain caller op) = net := by
  (simp? [NetworkState.applyAdv, h] says simp only [applyAdv, h])

@[simp] theorem NetworkState.applyAdv_deliver (apps : Apps E) {p : Participant}
    (net : NetworkState E p) (ss : SignedState E) :
    net.applyAdv apps (.deliver ss) = { net with received := ss :: net.received } := by
  rfl

theorem NetworkState.applyAdv_tick (apps : Apps E) {p : Participant}
    (net : NetworkState E p) (dt : Time) :
    net.applyAdv apps (.tick dt) = { net with chain := net.chain.tick dt } := by
  rfl

/-- `applyAdv` of `p`'s own pending call landing, when it succeeds. -/
@[simp] theorem NetworkState.applyAdv_land_some (apps : Apps E) {p : Participant}
    {net : NetworkState E p} {op : Op E} {s' : Adjudicator E}
    (h : net.chain.apply apps p op = some s') :
    net.applyAdv apps (.land op) = { net with chain := s', received := op.proofStates ++ net.received } := by
  (simp? [NetworkState.applyAdv, h] says simp only [applyAdv, h])

/-- `applyAdv` of `p`'s own pending call landing, when it fails. -/
@[simp] theorem NetworkState.applyAdv_land_none (apps : Apps E) {p : Participant}
    {net : NetworkState E p} {op : Op E}
    (h : net.chain.apply apps p op = none) :
    net.applyAdv apps (.land op) = net := by
  (simp? [NetworkState.applyAdv, h] says simp only [applyAdv, h])

/-- What the adversary can do. `feasible net m` holds when the adversary can
    play `m` from `net`. `ε` is the inclusion bound of Nitro:537-539: a
    transaction lands before `ε` has passed; the type carries `0 < ε`
    (Nitro:537 "ε > 0"). `feasible` is never consulted for `.land`
    (`Threat.RoundSeq.land` gates it structurally, by membership in the
    reaction's own pending calls, not by the adversary's say-so: Nitro's
    "unimpeded" assumption is a chain guarantee, not a favour the adversary
    grants). The structures `Bounds` and `Capable` bound `.chain`/`.deliver`;
    `Capable.capableTick` bounds `.tick` subject to `Threat.Round`. -/
structure Threat (E : Type) (p : Participant) where
  feasible : NetworkState E p → AdvMove E → Prop
  ε : Time
  ε_pos : 0 < ε

/-- A proof state `ss` is accepted by `p` in the proof `proof` when a later
    state of the same proof carries `p`'s signature: `p` moved on top of it.
    Design decision 2026-11-02: a payment that `p` has built on is accepted
    history, not an attack. -/
def SupportProof.AcceptedBy {p : Participant} (proof : SupportProof E) (ss : SignedState E) :
    Prop :=
  ∃ (i j : Nat) (t : SignedState E), proof[i]? = some ss ∧ i < j ∧ proof[j]? = some t ∧
    p ∈ t.signers

/-- An adversary move commits no own-violation of a participant other than
    `p`: every state it delivers, and every proof state of a call it makes,
    is no own-violation (`OwnViolation`, `ArmadaLean/Types/OwnViolation.lean`)
    of any of its signers other than `p`, against the states that `p`
    received and the other proof states of the call. In a call, a gift that
    `p` accepted in the same proof (`SupportProof.AcceptedBy`) does not
    count: the candidate's outcome comes from `p`'s last state and the clean
    moves after it, so an accepted gift cannot turn the candidate against
    `p`. A conflict always counts. -/
def AdvMove.NoOwnViolation {p : Participant} (dest : Participant → E) (net : NetworkState E p) :
    AdvMove E → Prop
  | .deliver ss => ∀ q ∈ ss.signers, q ≠ p → ¬ OwnViolation dest q net.received ss
  | .chain _ op => ∀ ss ∈ op.proofStates, ∀ q ∈ ss.signers, q ≠ p →
      ¬ OwnViolation.Conflict
          ((op.proofStates ++ net.received).filter fun s => decide (q ∈ s.signers)) ss.state ∧
        (SupportProof.AcceptedBy (p := p) op.proofStates ss ∨
          ¬ OwnViolation dest q (op.proofStates ++ net.received) ss)
  | _ => True

/-- A call whose proof states are no own-violations at all commits no
    own-violation. -/
theorem AdvMove.NoOwnViolation.chain_of {p : Participant} {dest : Participant → E}
    {net : NetworkState E p} {caller : Participant} {op : Op E}
    (h : ∀ ss ∈ op.proofStates, ∀ q ∈ ss.signers, q ≠ p →
      ¬ OwnViolation dest q (op.proofStates ++ net.received) ss) :
    (AdvMove.chain caller op).NoOwnViolation dest net :=
  fun ss hss q hq hqp => ⟨fun hc => h ss hss q hq hqp (Or.inl hc), Or.inr (h ss hss q hq hqp)⟩

/-- **The threat without own-violations of the other participants.**
    Design decision 2026-11-01: own-violation is one rule for every
    participant; a state signed against the signer's own interest costs only
    the signer and never defeats another participant's guarantee. An attacker's
    own-violation is griefing (ForceMove §4.5), not a clean attack. The
    derived threat plays only the moves of `T` that commit no such violation.
    A statement keeps `Assumptions apps p T` for `T` itself: the premise
    "`T` never violates" would contradict `Capable`, which makes every
    unforged move of another participant feasible. -/
def Threat.noOwnViolation {p : Participant} (T : Threat E p) (dest : Participant → E) :
    Threat E p where
  feasible net m := T.feasible net m ∧ m.NoOwnViolation dest net
  ε := T.ε
  ε_pos := T.ε_pos

/-- One round's adversary play while `p`'s reaction, issued at the round's
    own start time `t`, still has `pending` calls unlanded (Lamport's
    explicit-time form, CHARME 2005, quoted in this file's header). Three
    kinds of step: `land` takes one call out of `pending` — chosen anywhere
    among the adversary's own moves, in any order (front-running); `tick` is
    disabled once it would push the clock past `t + T.ε` while any call is
    still pending — the one new constraint this design decision adds, read literally
    off "an enabling condition on the Tick action"; every other adversary
    move (`.chain`, `.deliver`) is unconstrained by `pending`, exactly as in
    the one-move game (`other`). The round closes (`nil`) only once
    `pending` is empty: every call a reaction issues is, structurally,
    landed before the round can end. -/
inductive Threat.RoundSeq (apps : Apps E) {p : Participant} (T : Threat E p) (t : Time) :
    List (Op E) → NetworkState E p → NetworkState E p → Prop
  | nil {net} : Threat.RoundSeq apps T t [] net net
  | land {pending net net' op l1 l2} (hsplit : pending = l1 ++ op :: l2)
      (hrest : Threat.RoundSeq apps T t (l1 ++ l2) (net.applyAdv apps (.land op)) net') :
      Threat.RoundSeq apps T t pending net net'
  | tick {pending net net' dt} (hfeas : T.feasible net (.tick dt))
      (hgate : pending = [] ∨ net.chain.now + dt < t + T.ε)
      (hrest : Threat.RoundSeq apps T t pending (net.applyAdv apps (.tick dt)) net') :
      Threat.RoundSeq apps T t pending net net'
  | other {pending net net' m} (hfeas : T.feasible net m)
      (hnotick : ∀ dt, m ≠ .tick dt) (hnoland : ∀ op, m ≠ .land op)
      (hrest : Threat.RoundSeq apps T t pending (net.applyAdv apps m) net') :
      Threat.RoundSeq apps T t pending net net'

/-- The on-chain calls a move puts up for landing this round: a reaction's
    own `calls`, or none for `wait`. -/
def HonestMove.calls : HonestMove E → List (Op E)
  | .react r => r.calls
  | .wait _ => []

/-- A run of the round from `net` to `net'` (`Threat.RoundSeq`, `pending` issued at time `t`)
    that ends before `T.ε` has passed on `net`'s clock. The rest of a round, from any state
    inside it, is one too; the round lemmas of `Liveness.lean` take it. -/
structure Threat.TimedRun (apps : Apps E) {p : Participant} (T : Threat E p) (t : Time)
    (pending : List (Op E)) (net net' : NetworkState E p) : Prop where
  seq : Threat.RoundSeq apps T t pending net net'
  within : net'.chain.now < net.chain.now + T.ε

/-- One round: `p`'s move `m`, issued at `net`'s clock, has every one of its
    calls landed (`Threat.TimedRun`), and the round itself ends before
    `t + T.ε` has passed (Nitro:537-539, "before time t + ε") — the same
    bound `Threat.Round` always had, now read against the round's start
    rather than against a single call in isolation. `Threat.Round.single`
    shows the one-call case is exactly the old bound. -/
def Threat.Round (apps : Apps E) {p : Participant} (T : Threat E p) (m : HonestMove E)
    (net net' : NetworkState E p) : Prop :=
  Threat.TimedRun apps T net.chain.now m.calls net net'

/-- `Threat.Round` is the run of `m`'s calls and the time bound, the two facts it held
    before `Threat.TimedRun` carried them. -/
theorem Threat.Round_iff (apps : Apps E) {p : Participant} (T : Threat E p) (m : HonestMove E)
    (net net' : NetworkState E p) : Threat.Round apps T m net net' ↔
      Threat.RoundSeq apps T net.chain.now m.calls net net' ∧ net'.chain.now < net.chain.now + T.ε :=
  ⟨fun h => ⟨h.seq, h.within⟩, fun h => ⟨h.1, h.2⟩⟩

/-- A reaction with one call and no sends — today's single on-chain move. -/
def Reaction.one (op : Op E) : Reaction E := ⟨[op], []⟩

/-- Today's single on-chain move, as a reaction (`Reaction.one`). Dot
    notation resolves `.chain op`, written where a `HonestMove E` is
    expected, to this definition, so a one-call reaction is written exactly
    as the old game's single `.chain` move was. -/
def HonestMove.chain (op : Op E) : HonestMove E := .react (Reaction.one op)

/-- Today's single send move, as a reaction with no calls. Dot notation
    resolves `.send st` to this definition. -/
def HonestMove.send (st : State E) : HonestMove E := .react ⟨[], [st]⟩

omit [DecidableEq E] in
@[simp] theorem HonestMove.calls_chain (op : Op E) : (HonestMove.chain op).calls = [op] := rfl

omit [DecidableEq E] in
@[simp] theorem HonestMove.calls_send (st : State E) : (HonestMove.send st).calls = [] := rfl

omit [DecidableEq E] in
@[simp] theorem HonestMove.calls_wait (dt : Time) : (HonestMove.wait (E := E) dt).calls = [] := rfl

@[simp] theorem HonestMove.Feasible_chain {p : Participant} (apps : Apps E) (net : NetworkState E p)
    (op : Op E) : (HonestMove.chain op).Feasible apps net ↔ op.HonestFeasible net := by
  simp only [HonestMove.Feasible, HonestMove.chain, Reaction.one, Reaction.Feasible, List.mem_cons,
    List.not_mem_nil, or_false, forall_eq, Reaction.SendsHonest, List.map_nil, List.nil_append,
    IsEmpty.forall_iff, implies_true, and_true]

/-- One send is feasible exactly when it satisfies the signing rules
    (`HonestSend`) against `p`'s sent states with itself added. -/
@[simp] theorem HonestMove.Feasible_send {p : Participant} (apps : Apps E) (net : NetworkState E p)
    (st : State E) : (HonestMove.send st).Feasible apps net ↔
      HonestSend (⟨st, [p]⟩ :: net.sent) net.HoldsPrefund (net.CanMoveTo apps) st := by
  simp only [HonestMove.Feasible, HonestMove.send, Reaction.Feasible, List.not_mem_nil,
    IsEmpty.forall_iff, implies_true, Reaction.SendsHonest, List.mem_cons, or_false, List.map_cons,
    List.map_nil, List.cons_append, List.nil_append, forall_eq, true_and]

omit [DecidableEq E] in
/-- A send has no calls, so its calls are feasible (`HonestMove.CallsFeasible`). -/
@[simp] theorem HonestMove.CallsFeasible_send {p : Participant} (net : NetworkState E p)
    (st : State E) : (HonestMove.send st).CallsFeasible net :=
  fun _ h => absurd h List.not_mem_nil

omit [DecidableEq E] in
@[simp] theorem NetworkState.applyHonest_chain {p : Participant} (net : NetworkState E p)
    (op : Op E) : net.applyHonest (HonestMove.chain op) = net := by
  (simp? [NetworkState.applyHonest, HonestMove.chain, Reaction.one] says simp only [applyHonest, HonestMove.chain, Reaction.one, List.map_nil, List.nil_append])

omit [DecidableEq E] in
@[simp] theorem NetworkState.applyHonest_send {p : Participant} (net : NetworkState E p)
    (st : State E) : net.applyHonest (HonestMove.send st) = { net with sent := ⟨st, [p]⟩ :: net.sent } := by
  (simp? [NetworkState.applyHonest, HonestMove.send] says simp only [applyHonest, HonestMove.send, List.map_cons, List.map_nil, List.cons_append, List.nil_append])

/-- A `RoundSeq` derivation, when its pending list is non-empty, is: a run of
    ordinary adversary moves (`tick`/`other`, no land) up to the FIRST call
    the adversary actually lands — some `op` sitting at `pending = l1 ++ op
    :: l2` — then the rest, with `op` cleared from `pending`. The base case
    (`land` is the derivation's own first step) needs no induction; `tick`
    and `other` just carry the found split through unchanged, prepending
    their own step ahead of the found land.

    The lemma reports WHICH call landed first instead of fixing an order
    ahead of time, because two land calls do not commute in general:
    `Adjudicator.deposit`'s `expectedHeld` guard (`Adjudicator.lean:108`)
    makes a second deposit's success depend on whether an earlier one to
    the same channel already landed, so "pending1 always lands before
    pending2" is false for an arbitrary split of an arbitrary pending list.
    `peel_one` and `peel_two` both specialize this one lemma by a short
    case split on the reported position `l1`, instead of re-running the
    induction each time. -/
theorem Threat.RoundSeq.peel_split {apps : Apps E} {p : Participant} {T : Threat E p} {t : Time}
    {pending : List (Op E)} {n0 n2 : NetworkState E p} (hne : pending ≠ [])
    (hseq : Threat.RoundSeq apps T t pending n0 n2) :
    ∃ l1 op l2, pending = l1 ++ op :: l2 ∧
      ∃ n1, Threat.RoundSeq apps T t [] n0 n1 ∧
        Threat.RoundSeq apps T t (l1 ++ l2) (n1.applyAdv apps (.land op)) n2 := by
  induction hseq with
  | nil => exact absurd rfl hne
  | @land pending n net' op l1 l2 hsplit hrest _ =>
    exact ⟨l1, op, l2, hsplit, n, Threat.RoundSeq.nil, hrest⟩
  | @tick pending n net' dt hfeas hgate hrest ih =>
    obtain ⟨l1, op, l2, heq, n1, hA, hB⟩ := ih hne
    exact ⟨l1, op, l2, heq, n1, Threat.RoundSeq.tick hfeas (Or.inl rfl) hA, hB⟩
  | @other pending n net' m hfeas hnotick hnoland hrest ih =>
    obtain ⟨l1, op, l2, heq, n1, hA, hB⟩ := ih hne
    exact ⟨l1, op, l2, heq, n1, Threat.RoundSeq.other hfeas hnotick hnoland hA, hB⟩

/-- One call always peels off a `RoundSeq` as the LAST pending-clearing
    step: `[op]` has only one way to split, so every `land` step on
    `pending = [op]` consumes it whole, leaving `[]`. `peel_split` finds
    the split; a singleton pending list has only the empty one. -/
theorem Threat.RoundSeq.peel_one {apps : Apps E} {p : Participant} {T : Threat E p} {t : Time}
    (op : Op E) (n0 n2 : NetworkState E p) (hseq : Threat.RoundSeq apps T t [op] n0 n2) :
    ∃ n1, Threat.RoundSeq apps T t [] n0 n1 ∧
      Threat.RoundSeq apps T t [] (n1.applyAdv apps (.land op)) n2 := by
  obtain ⟨l1, op', l2, heq, n1, hA, hB⟩ :=
    Threat.RoundSeq.peel_split (pending := [op]) (by (simp? says simp only [ne_eq, List.cons_ne_self, not_false_eq_true])) hseq
  rcases l1 with _ | ⟨a, l1⟩
  · simp only [List.nil_append, List.cons.injEq, List.nil_eq] at heq
    obtain ⟨heqop, heql2⟩ := heq
    subst heqop; subst heql2
    simp only [List.nil_append] at hB
    exact ⟨n1, hA, hB⟩
  · (simp? at heq says simp only [List.cons_append, List.cons.injEq, List.nil_eq, List.append_eq_nil_iff, reduceCtorEq, and_false] at heq)

/-- Two calls peel off a `RoundSeq` one at a time, in whichever order the
    adversary front-runs them (Nitro:540-542): `pending = [opA, opB]` splits
    at a `land` step either on `opA` (leaving `[opB]` still pending) or on
    `opB` (leaving `[opA]`), with ordinary adversary play (`tick`/`other`)
    before that first `land` — `peel_split`'s own split, specialized to a
    two-element pending list, which has only those two positions.
    `satp_intermediary_before_round2`'s two-call reaction peels through
    this, independently of which of its two calls the adversary lands
    first. -/
theorem Threat.RoundSeq.peel_two {apps : Apps E} {p : Participant} {T : Threat E p} {t : Time}
    (opA opB : Op E) (n0 n3 : NetworkState E p)
    (hseq : Threat.RoundSeq apps T t [opA, opB] n0 n3) :
    (∃ n1, Threat.RoundSeq apps T t [] n0 n1 ∧
      Threat.RoundSeq apps T t [opB] (n1.applyAdv apps (.land opA)) n3) ∨
    (∃ n1, Threat.RoundSeq apps T t [] n0 n1 ∧
      Threat.RoundSeq apps T t [opA] (n1.applyAdv apps (.land opB)) n3) := by
  obtain ⟨l1, op, l2, heq, n1, hA, hB⟩ :=
    Threat.RoundSeq.peel_split (pending := [opA, opB]) (by (simp? says simp only [ne_eq, reduceCtorEq, not_false_eq_true])) hseq
  rcases l1 with _ | ⟨a, l1⟩
  · simp only [List.nil_append, List.cons.injEq] at heq
    obtain ⟨heqop, heql2⟩ := heq
    subst heqop; subst heql2
    exact Or.inl ⟨n1, hA, hB⟩
  · rcases l1 with _ | ⟨b, l1⟩
    · simp only [List.cons_append, List.nil_append, List.cons.injEq, List.nil_eq] at heq
      obtain ⟨heqa, heqop, heql2⟩ := heq
      subst heqa; subst heqop; subst heql2
      simp only [List.append_nil] at hB
      exact Or.inr ⟨n1, hA, hB⟩
    · (simp? at heq says simp only [List.cons_append, List.cons.injEq, List.nil_eq, List.append_eq_nil_iff, reduceCtorEq, and_false] at heq)

/-- An adversary move never moves the chain's clock backward: only `tick`
    touches it, and only forward (`Adjudicator.apply_now_le`). -/
theorem NetworkState.applyAdv_now_le (apps : Apps E) {p : Participant}
    (net : NetworkState E p) (m : AdvMove E) :
    net.chain.now ≤ (net.applyAdv apps m).chain.now := by
  cases m with
  | chain caller op =>
    simp only [NetworkState.applyAdv]
    cases h : net.chain.apply apps caller op with
    | none => exact le_refl _
    | some s' => (simpa? using Adjudicator.apply_now_le h says simpa only using Adjudicator.apply_now_le h)
  | deliver ss => exact le_refl _
  | tick dt => simp only [NetworkState.applyAdv, Adjudicator.tick_now]; exact Nat.le_add_right _ _
  | land op =>
    simp only [NetworkState.applyAdv]
    cases h : net.chain.apply apps p op with
    | none => exact le_refl _
    | some s' => (simpa? using Adjudicator.apply_now_le h says simpa only using Adjudicator.apply_now_le h)

/-- Over a round's adversary play (`Threat.RoundSeq`, any pending calls),
    the chain's clock only advances (`NetworkState.applyAdv_now_le`, by
    induction over `land`/`tick`/`other`: each is one `NetworkState.applyAdv`
    step). -/
theorem Threat.RoundSeq.now_le {apps : Apps E} {p : Participant} {T : Threat E p} {t : Time}
    {pending : List (Op E)} {net net' : NetworkState E p}
    (h : T.RoundSeq apps t pending net net') : net.chain.now ≤ net'.chain.now := by
  induction h with
  | nil => exact le_refl _
  | land _ _ ih => exact le_trans (NetworkState.applyAdv_now_le _ _ _) ih
  | tick _ _ _ ih => exact le_trans (NetworkState.applyAdv_now_le _ _ _) ih
  | other _ _ _ _ ih => exact le_trans (NetworkState.applyAdv_now_le _ _ _) ih

/-- **The step obligations of a round invariant.** Each kind of step a `Threat.RoundSeq`
    derivation can take preserves `Inv`: the honest participant's own pending call landing
    (`land`, from a state where the side condition `Cond` holds of that call), an adversary
    `.deliver`, an adversary `.tick`, and an adversary `.chain` call by another participant.
    Every obligation also receives `Guard n` for the step's own start state `n`. The round
    combinators below set `Guard` to "the clock has not passed the round's own end"
    (`Threat.RoundSeq.now_le` on the rest of the derivation), so a family that needs a
    deadline still ahead of the ROUND's end reads it off `Guard`; the strategy-tree form
    (`UnbeatableIn.and_condInvariant`) sets `Guard := fun _ => True`. A
    family states its one-step lemmas once, as one value of this structure, and every
    combinator variant takes that value (`docs/lean/type-doctrine.md` rule 1). -/
structure Threat.StepInvariant (apps : Apps E) {p : Participant} (T : Threat E p)
    (Guard Inv : NetworkState E p → Prop) (Cond : NetworkState E p → Op E → Prop) : Prop where
  land : ∀ {n : NetworkState E p} {op : Op E}, Guard n → Cond n op → Inv n →
    Inv (n.applyAdv apps (.land op))
  deliver : ∀ {n : NetworkState E p} {ss : SignedState E}, Guard n →
    T.feasible n (.deliver ss) → Inv n → Inv (n.applyAdv apps (.deliver ss))
  tick : ∀ {n : NetworkState E p} {dt : Time}, Guard n → T.feasible n (.tick dt) → Inv n →
    Inv (n.applyAdv apps (.tick dt))
  chain : ∀ {n : NetworkState E p} {caller : Participant} {op : Op E}, Guard n →
    T.feasible n (.chain caller op) → Inv n → Inv (n.applyAdv apps (.chain caller op))

/-- **The side-condition variant.** A `Threat.StepInvariant` whose `land` side condition
    `Cond` survives every adversary move (`condMono`), so a round combinator needs `Cond`
    only once, for the round's own `pending` list at its start. Every family's `Cond` so far
    -- `Op.HonestFeasible`, "targets a channel other than X" -- is either monotone as `Holds`
    grows or does not mention the network at all. -/
structure Threat.CondStepInvariant (apps : Apps E) {p : Participant} (T : Threat E p)
    (Guard Inv : NetworkState E p → Prop) (Cond : NetworkState E p → Op E → Prop) : Prop
    extends Threat.StepInvariant apps T Guard Inv Cond where
  condMono : ∀ {n : NetworkState E p} {op : Op E} (m : AdvMove E), Cond n op →
    Cond (n.applyAdv apps m) op

/-- An obligation proved from every state holds under any `Guard`: the strategy-tree form
    proves its obligations with `Guard := fun _ => True` and passes them to the round
    combinator, which fixes `Guard` to the round's own clock bound. -/
theorem Threat.StepInvariant.anyGuard {apps : Apps E} {p : Participant} {T : Threat E p}
    {Guard Inv : NetworkState E p → Prop} {Cond : NetworkState E p → Op E → Prop}
    (h : T.StepInvariant apps (fun _ => True) Inv Cond) : T.StepInvariant apps Guard Inv Cond :=
  ⟨fun _ => h.land trivial, fun _ => h.deliver trivial, fun _ => h.tick trivial,
    fun _ => h.chain trivial⟩

/-- **Conjunction of step invariants.** `I1`'s obligations, and `I2`'s obligations proved
    with `I1` at the step's own start state as an extra guard, give the obligations of
    `I1 ∧ I2`. A family reuses a named invariant (`I1`) and states only what it adds (`I2`).
    This also closes the "ratchet" families (`Nitro/Liveness.lean`, SATP): `I1` carries
    "`r.V` is live at the round's end", so a disjunct of `I2` that records an escalation
    witness needs no second induction to show `r.V` stays unfinalized. -/
theorem Threat.StepInvariant.and {apps : Apps E} {p : Participant} {T : Threat E p}
    {Guard I1 I2 : NetworkState E p → Prop} {Cond : NetworkState E p → Op E → Prop}
    (h1 : T.StepInvariant apps Guard I1 Cond)
    (h2 : T.StepInvariant apps (fun n => Guard n ∧ I1 n) I2 Cond) :
    T.StepInvariant apps Guard (fun n => I1 n ∧ I2 n) Cond :=
  ⟨fun hg hc hI => ⟨h1.land hg hc hI.1, h2.land ⟨hg, hI.1⟩ hc hI.2⟩,
    fun hg hf hI => ⟨h1.deliver hg hf hI.1, h2.deliver ⟨hg, hI.1⟩ hf hI.2⟩,
    fun hg hf hI => ⟨h1.tick hg hf hI.1, h2.tick ⟨hg, hI.1⟩ hf hI.2⟩,
    fun hg hf hI => ⟨h1.chain hg hf hI.1, h2.chain ⟨hg, hI.1⟩ hf hI.2⟩⟩

/-- **The round combinator.** An invariant `Inv` whose step obligations hold
    (`Threat.CondStepInvariant`, guarded by the round's own end clock) holds when the round
    ends whenever it held at its start and `Cond` held of every pending call at the start.
    The one induction over `Threat.RoundSeq`; `Threat.RoundSeq.nil_invariant` specializes
    it. -/
theorem Threat.RoundSeq.condInvariant {apps : Apps E} {p : Participant} {T : Threat E p}
    {t : Time} {pending : List (Op E)} {net net' : NetworkState E p}
    {Inv : NetworkState E p → Prop} {Cond : NetworkState E p → Op E → Prop}
    (hseq : Threat.RoundSeq apps T t pending net net')
    (h : T.CondStepInvariant apps (fun n => n.chain.now ≤ net'.chain.now) Inv Cond)
    (hcond : ∀ op ∈ pending, Cond net op) (hI : Inv net) : Inv net' := by
  induction hseq with
  | nil => exact hI
  | @land pending n1 n2 op l1 l2 hsplit hrest ih =>
    have hg : n1.chain.now ≤ n2.chain.now :=
      le_trans (NetworkState.applyAdv_now_le apps n1 (.land op)) hrest.now_le
    refine ih h (fun op' hop' => h.condMono (.land op) (hcond op' ?_))
      (h.land hg (hcond op (by
        rw [hsplit]; simp only [List.mem_append, List.mem_cons, true_or, or_true])) hI)
    rw [hsplit]; simp only [List.mem_append, List.mem_cons] at hop' ⊢; tauto
  | @tick pending n1 n2 dt hfeas hgate hrest ih =>
    exact ih h (fun op' hop' => h.condMono (.tick dt) (hcond op' hop'))
      (h.tick (le_trans (NetworkState.applyAdv_now_le apps n1 (.tick dt)) hrest.now_le) hfeas hI)
  | @other pending n1 n2 m hfeas hnotick hnoland hrest ih =>
    have hg : n1.chain.now ≤ n2.chain.now :=
      le_trans (NetworkState.applyAdv_now_le apps n1 m) hrest.now_le
    refine ih h (fun op' hop' => h.condMono m (hcond op' hop')) ?_
    cases m with
    | tick dt => exact absurd rfl (hnotick dt)
    | land op => exact absurd rfl (hnoland op)
    | deliver ss => exact h.deliver hg hfeas hI
    | chain caller op => exact h.chain hg hfeas hI

/-- `Threat.RoundSeq.condInvariant` on a sub-round of pure adversary play (`pending = []`):
    `land` cannot happen there, so the caller's `land` obligation is the vacuous one for
    `Cond := fun _ _ => False`. Replaces the `generalize`/`induction` scaffold each
    `_nil`/`_roundSeq` family copied (`Nitro/Liveness.lean`). -/
theorem Threat.RoundSeq.nil_invariant {apps : Apps E} {p : Participant} {T : Threat E p} {t : Time}
    {net net' : NetworkState E p} {Inv : NetworkState E p → Prop}
    (hseq : Threat.RoundSeq apps T t [] net net')
    (h : T.StepInvariant apps (fun n => n.chain.now ≤ net'.chain.now) Inv (fun _ _ => False))
    (hI : Inv net) : Inv net' :=
  hseq.condInvariant ⟨h, fun _ hc => hc⟩
    (by simp only [List.not_mem_nil, imp_self, implies_true]) hI

/-- **The old per-move bound is `Threat.Round`'s one-call special case.**
    For a reaction with one call (`HonestMove.chain op`, `pending = [op]`),
    `Threat.RoundSeq.peel_one` splits the round into ordinary adversary
    moves, the single step that lands `op`, then more ordinary adversary
    moves — exactly the old game's shape (a feasible prefix, `op` applied
    once, a feasible suffix), except the new game also lets a strategy
    proof move suffix moves to the OTHER side of the landing: it is a
    genuinely more adversarial game, not merely a restatement. -/
theorem Threat.Round.single {apps : Apps E} {p : Participant} {T : Threat E p} {op : Op E}
    {net net' : NetworkState E p} (h : T.Round apps (HonestMove.chain op) net net') :
    ∃ net1, Threat.RoundSeq apps T net.chain.now [] net net1 ∧
      Threat.RoundSeq apps T net.chain.now [] (net1.applyAdv apps (.land op)) net' := by
  obtain ⟨hseq, -⟩ := h
  simp only [HonestMove.calls_chain] at hseq
  exact Threat.RoundSeq.peel_one op net net' hseq

/-- Landing every call of `pending`, in order, with no `tick` and no other
    adversary move, is always a valid way to run a round out to `nil` —
    `.land` is never gated by `T.feasible` (`Threat.RoundSeq.land`), only
    by membership in `pending` — and, PROVIDED none of those calls is
    itself `.tick`, this particular round never moves the clock
    (`apply_now_eq_of_not_tick`, `Lemmas.lean`): landing an op that is not
    `.tick` only ever writes `balances`/`status`. This is a fact about the
    ONE derivation this theorem builds, not every `Threat.RoundSeq`
    derivation — the adversary's own `tick`/`other` steps genuinely do
    move the clock in other derivations; this one simply never uses them.
    Used by `Threat.Round.exists`. -/
theorem Threat.RoundSeq.landAll (apps : Apps E) {p : Participant} (T : Threat E p) (t : Time) :
    ∀ (pending : List (Op E)), (∀ op ∈ pending, ∀ dt, op ≠ Op.tick dt) →
      ∀ (net : NetworkState E p),
        ∃ net', Threat.RoundSeq apps T t pending net net' ∧ net'.chain.now = net.chain.now := by
  intro pending
  induction pending with
  | nil => intro _ net; exact ⟨net, Threat.RoundSeq.nil, rfl⟩
  | cons op rest ih =>
    intro hnotick net
    have hop : ∀ dt, op ≠ Op.tick dt := hnotick op List.mem_cons_self
    have heq1 : (net.applyAdv apps (.land op)).chain.now = net.chain.now := by
      simp only [NetworkState.applyAdv]
      cases h : net.chain.apply apps p op with
      | none => rfl
      | some s' => exact Adjudicator.apply_now_eq_of_not_tick hop h
    obtain ⟨net', hrest, heq2⟩ := ih (fun op' hop' => hnotick op' (List.mem_cons_of_mem op hop'))
      (net.applyAdv apps (.land op))
    exact ⟨net', Threat.RoundSeq.land (l1 := []) (l2 := rest) rfl hrest, by rw [heq2, heq1]⟩

/-- **Every feasible reaction admits a round.** Landing every call of `m`
    at once, with no `tick`, never moves the clock
    (`Threat.RoundSeq.landAll`): every call `p` may issue excludes `.tick`
    (`Op.HonestFeasible`), precisely so this holds — a reaction that could
    only close by landing a `.tick` call would force the clock past its
    own deadline just to land it, making `Threat.Round` unsatisfiable for
    that move and every `UnbeatableIn` goal past it vacuously "unbeatable"
    (soundness finding, this design decision's own review). With the clock
    unmoved, the round's own bound (`net'.chain.now < net.chain.now +
    T.ε`) is `T.ε_pos`. -/
theorem Threat.Round.exists {apps : Apps E} {p : Participant} (T : Threat E p)
    {m : HonestMove E} {net : NetworkState E p} (hfeas : m.Feasible apps net) :
    ∃ net', T.Round apps m net net' := by
  have hnotick : ∀ op ∈ m.calls, ∀ dt, op ≠ Op.tick dt := by
    cases m with
    | react r =>
      intro op hop dt heq
      have := hfeas.1 op hop
      rw [heq] at this
      exact this
    | wait dt' => intro op hop; (simp? [HonestMove.calls] at hop says simp only [HonestMove.calls, List.not_mem_nil] at hop)
  obtain ⟨net', hseq, heq⟩ := Threat.RoundSeq.landAll apps T net.chain.now m.calls hnotick net
  refine ⟨net', hseq, ?_⟩
  rw [heq]
  exact Nat.lt_add_of_pos_right T.ε_pos

/-- The signatures of `p` that a state carries are genuine: `p` signed the
    state, and `p` signed a state that carries the state's voucher, if `p` is
    one of its signers. SATP:168: "(Safety) Forging cryptographic signatures
    is infeasible."; Nitro:158-160; ForceMove:683. -/
def NetworkState.Unforged {p : Participant} (net : NetworkState E p) (ss : SignedState E) : Prop :=
  (p ∈ ss.signers → ∃ s ∈ net.sent, s.state = ss.state) ∧
  ∀ v, ss.state.voucher? = some v → p ∈ v.signers → ∃ s ∈ net.sent, s.state.voucher? = some v

/-- A held state's own unforged-ness follows from the unforged-ness of every
    already-received state: `Holds`'s signer clause either points straight at
    `net.sent` or at a received state carrying the same signer, whose own
    `Unforged` (by hypothesis) closes the loop. Likewise for the voucher
    clause. -/
theorem NetworkState.Holds.unforged {p : Participant} {net : NetworkState E p}
    {ss : SignedState E} (hH : net.Holds ss)
    (hind : ∀ r ∈ net.received, net.Unforged r) : net.Unforged ss := by
  constructor
  · intro hp
    rcases hH.1 p hp with ⟨-, hs⟩ | ⟨r, hr, hreq, hrsig⟩
    · exact hs
    · obtain ⟨s, hs, hseq⟩ := (hind r hr).1 hrsig
      exact ⟨s, hs, hseq.trans hreq⟩
  · intro v hv hp
    rcases hH.2 v hv p hp with ⟨-, hs⟩ | ⟨r, hr, hrv⟩
    · exact hs
    · exact (hind r hr).2 v hrv hp

omit [DecidableEq E] in
/-- `Unforged` depends only on `net.sent`: lift it across a step that
    leaves `sent` unchanged, regardless of what else moves. -/
theorem NetworkState.Unforged.of_sent {p : Participant} {net net' : NetworkState E p}
    {ss : SignedState E} (hs : net.sent = net'.sent) (h : net.Unforged ss) : net'.Unforged ss := by
  unfold NetworkState.Unforged at *
  rw [← hs]
  exact h

omit [DecidableEq E] in
/-- `Unforged` lifts across a step that only GROWS `sent` (e.g. an honest
    `.react`, which appends freshly-sent states but never removes an
    existing one): a witness in the smaller `net.sent` is still a witness
    in the larger `net'.sent`. -/
theorem NetworkState.Unforged.mono {p : Participant} {net net' : NetworkState E p}
    {ss : SignedState E} (hs : net.sent ⊆ net'.sent) (h : net.Unforged ss) : net'.Unforged ss := by
  unfold NetworkState.Unforged at *
  exact ⟨fun hp => (h.1 hp).imp (fun s ⟨hmem, heq⟩ => ⟨hs hmem, heq⟩),
    fun v hv hp => (h.2 v hv hp).imp (fun s ⟨hmem, heq⟩ => ⟨hs hmem, heq⟩)⟩

/-- The bounds on the adversary `T`, as named hypotheses. -/
structure Bounds (apps : Apps E) (p : Participant) (T : Threat E p) : Prop where
  /-- SATP:168, Nitro:158-160, ForceMove:683: the adversary submits a
      signature of `p` only where `p` signed. -/
  unforgeable : ∀ net caller op, T.feasible net (.chain caller op) →
    ∀ ss ∈ op.proofStates, net.Unforged ss
  /-- The same bound for delivered states. -/
  unforgeableDeliver : ∀ net ss, T.feasible net (.deliver ss) → net.Unforged ss
  /-- The adversary never acts as `p`. -/
  notHonest : ∀ net caller op, T.feasible net (.chain caller op) → caller ≠ p

/-- The derived threat `T.noOwnViolation dest` plays only moves of `T`, so it
    keeps the bounds of `T`. -/
theorem Bounds.noOwnViolation {apps : Apps E} {p : Participant} {T : Threat E p}
    (B : Bounds apps p T) (dest : Participant → E) : Bounds apps p (T.noOwnViolation dest) :=
  ⟨fun net caller op h => B.unforgeable net caller op h.1, fun net ss h => B.unforgeableDeliver net ss h.1,
    fun net caller op h => B.notHonest net caller op h.1⟩

/-- The capabilities of the adversary `T`. Nitro:460-461: the adversary
    controls every other participant. -/
structure Capable (apps : Apps E) (p : Participant) (T : Threat E p) : Prop where
  /-- Any operation by another caller that carries no forged signature of
      `p` is feasible. -/
  capable : ∀ net caller op, caller ≠ p → (∀ ss ∈ op.proofStates, net.Unforged ss) →
    T.feasible net (.chain caller op)
  /-- The adversary can deliver any state it can sign. -/
  capableDeliver : ∀ net ss, net.Unforged ss → T.feasible net (.deliver ss)
  /-- The adversary can move the clock; `Threat.Round` bounds each round. -/
  capableTick : ∀ net dt, T.feasible net (.tick dt)
  /-- The clock runs (Nitro:535-537 "before time
      t + ε", SATP:165-166): a round has room for a tick of at least 1 before
      `t + ε`. -/
  clockRuns : 2 ≤ T.ε

/-- The chain and cryptography assumptions of the full game. Each theorem
    that speaks about a strategy takes an `Assumptions` value. -/
structure Assumptions (apps : Apps E) (p : Participant) (T : Threat E p) : Prop
    extends Bounds apps p T, Capable apps p T

/-- Nitro:526-530: "having an unbeatable strategy for obtaining some state
    on-chain. The means that whatever actions (or lack of actions) other
    participants and external parties might take, the target state is still
    obtainable." `UnbeatableIn apps T allowed G net`: `p` has a strategy from
    `net`, using only moves in `allowed`, that reaches a state in `G` against
    every feasible adversary play. The strategy is the finite tree of honest
    moves. -/
inductive UnbeatableIn (apps : Apps E) {p : Participant} (T : Threat E p)
    (allowed : HonestMove E → Prop) (G : NetworkState E p → Prop) : NetworkState E p → Prop
  | done {net} : G net → UnbeatableIn apps T allowed G net
  | move {net} (m : HonestMove E) : allowed m → m.Feasible apps net →
      (∀ net', T.Round apps m net net' →
        UnbeatableIn apps T allowed G (net'.applyHonest m)) →
      UnbeatableIn apps T allowed G net

/-- `p` moves the clock itself: after one `.wait 1`, the clock is later than
    now, whatever the adversary does in the round. With `Capable.clockRuns`,
    no party stops the clock: the adversary can tick in every round, and `p`
    can always wait. -/
theorem UnbeatableIn.clock_advances (apps : Apps E) {p : Participant} (T : Threat E p)
    (net : NetworkState E p) :
    UnbeatableIn apps T (fun _ => True) (fun n => net.chain.now < n.chain.now) net := by
  refine UnbeatableIn.move (.wait 1) trivial trivial fun n' hround => UnbeatableIn.done ?_
  have hle : net.chain.now ≤ n'.chain.now := hround.1.now_le
  show net.chain.now < n'.chain.now + 1
  exact Nat.lt_succ_of_le hle

/-- `UnbeatableIn` with every honest move allowed. -/
def Unbeatable (apps : Apps E) {p : Participant} (T : Threat E p)
    (G : NetworkState E p → Prop) (net : NetworkState E p) : Prop :=
  UnbeatableIn apps T (fun _ => True) G net

/-- A strategy of `p`: the next move, in every network state. -/
def Strategy (E : Type) (p : Participant) := NetworkState E p → HonestMove E

/-- The states at the start of each round of a play of `σ`: each round is an
    adversary round (`Threat.Round`) landing the move `σ` chose at the
    start of the round. -/
inductive Run (apps : Apps E) {p : Participant} (T : Threat E p) (σ : Strategy E p) :
    NetworkState E p → NetworkState E p → Prop
  | refl {net} : Run apps T σ net net
  | round {net n1 n2} : Run apps T σ net n1 → T.Round apps (σ n1) n1 n2 →
      Run apps T σ net (n2.applyHonest (σ n1))

/-- **A strategy tree's own invariant, with a per-call side condition.** The `UnbeatableIn`
    form of `Threat.RoundSeq.condInvariant`, over `UnbeatableIn`'s own `done`/`move`
    induction: `Cond` for each round's own `pending` (`m.calls`) comes from `hcondfeas`,
    applied to that round's own `allowed m`/`m.Feasible` witnesses (`UnbeatableIn.move`'s own
    hypotheses). `hhonest` needs `Inv` kept only by the allowed honest moves: a family that
    reads `sent` allows no sends. Matches `UnbeatableIn.and_reachable`'s shape
    (`Nitro/Liveness.lean`), with `Cond n op := op.HonestFeasible n`. -/
theorem UnbeatableIn.and_condInvariant {apps : Apps E} {p : Participant} {T : Threat E p}
    {allowed : HonestMove E → Prop} {G : NetworkState E p → Prop} {Inv : NetworkState E p → Prop}
    {Cond : NetworkState E p → Op E → Prop}
    (h : T.CondStepInvariant apps (fun _ => True) Inv Cond)
    (hcondfeas : ∀ {n : NetworkState E p} {m : HonestMove E}, allowed m → m.Feasible apps n →
      ∀ op ∈ m.calls, Cond n op)
    (hhonest : ∀ {n : NetworkState E p} {m : HonestMove E}, allowed m → Inv n →
      Inv (n.applyHonest m))
    {net : NetworkState E p} (hU : UnbeatableIn apps T allowed G net) (hI : Inv net) :
    UnbeatableIn apps T allowed (fun n => G n ∧ Inv n) net := by
  induction hU with
  | done hG => exact UnbeatableIn.done ⟨hG, hI⟩
  | move m hal hfeas _ ih =>
    refine UnbeatableIn.move m hal hfeas fun net' hround => ih net' hround ?_
    exact hhonest hal (hround.1.condInvariant ⟨h.toStepInvariant.anyGuard, h.condMono⟩
      (hcondfeas hal hfeas) hI)

/-- Nitro:641-644: `p` "has a strategy to prevent" `G`: a strategy whose
    every move is feasible keeps every state of every play outside `G`,
    within the rounds too. -/
def Prevents (apps : Apps E) {p : Participant} (T : Threat E p)
    (G : NetworkState E p → Prop) (net : NetworkState E p) : Prop :=
  ∃ σ : Strategy E p, (∀ n, (σ n).Feasible apps n) ∧
    ∀ n1 n2, Run apps T σ net n1 → T.Round apps (σ n1) n1 n2 → ¬ G n2

/-- Nitro:602-603 `⟦χ ↦ Ω⟧`: `χ` finalized with the outcome `Ω`. A later
    payout does not change it. -/
def NetworkState.Finalized {p : Participant} (net : NetworkState E p) (c : FixedPart)
    (Ω : Outcome E) : Prop :=
  net.chain.finalizedWith c.address = some Ω

/-- A running challenge of `c` ends no sooner than `δ` from now. With
    `δ = ε`, `p` can answer it before it ends (Nitro:537-539). -/
def NetworkState.DeadlineAfter {p : Participant} (net : NetworkState E p) (c : FixedPart)
    (δ : Time) : Prop :=
  ∀ t ch, net.chain.statusOf c = .challenged t ch → net.chain.now + δ ≤ ch.deadline

/-- Nitro:590-593: "an outcome, Ω, is finalizable for participant A, if A has an
    unbeatable strategy for finalizing this outcome in the adjudicator. We use
    the notation `[χ ↦ Ω]_A`". -/
def Finalizable (apps : Apps E) {p : Participant} (T : Threat E p) (c : FixedPart) (Ω : Outcome E)
    (net : NetworkState E p) : Prop :=
  Unbeatable apps T (fun net' => net'.Finalized c Ω) net

/-- Nitro:641-652: "The enabled outcomes for a participant, p, is defined as the
    set of outcomes that p has no strategy to prevent from being finalized." -/
def Enabled (apps : Apps E) {p : Participant} (T : Threat E p) (c : FixedPart) (Ω : Outcome E)
    (net : NetworkState E p) : Prop :=
  ¬ Prevents apps T (fun net' => net'.Finalized c Ω) net

/-- `p` reaches `G` by playing the one strategy `σ`, against every feasible
    adversary play: `UnbeatableIn` with each move fixed to `σ`'s choice. -/
inductive UnbeatableBy (apps : Apps E) {p : Participant} (T : Threat E p) (σ : Strategy E p)
    (G : NetworkState E p → Prop) : NetworkState E p → Prop
  | done {net} : G net → UnbeatableBy apps T σ G net
  | move {net} : (σ net).Feasible apps net →
      (∀ net', T.Round apps (σ net) net net' → UnbeatableBy apps T σ G (net'.applyHonest (σ net))) →
      UnbeatableBy apps T σ G net

/-- The outcomes that some play of `σ` finalizes: the enabled outcomes of
    Nitro:641-652, measured against `p`'s own strategy `σ` and not against
    every strategy at once. Against every strategy, each outcome can need a
    different strategy to prevent it, and no single strategy then prevents
    them all (`docs/counterexamples/proposal_escape.lean`). -/
def EnabledBy (apps : Apps E) {p : Participant} (T : Threat E p) (σ : Strategy E p) (c : FixedPart)
    (Ω : Outcome E) (net : NetworkState E p) : Prop :=
  ∃ n, Run apps T σ net n ∧ n.Finalized c Ω

/-- A play of `σ` after its first round is a play of `σ` from the start. -/
theorem Run.cons {apps : Apps E} {p : Participant} {T : Threat E p} {σ : Strategy E p}
    {net n' n : NetworkState E p} (hr : T.Round apps (σ net) net n')
    (h : Run apps T σ (n'.applyHonest (σ net)) n) : Run apps T σ net n := by
  generalize hx : n'.applyHonest (σ net) = x at h
  induction h with
  | refl => subst hx; exact .round .refl hr
  | round _ h2 ih => exact .round ih h2

/-- What `σ` reaching `G` gives: some play of `σ` reaches `G` (every round
    has a play, `Threat.Round.exists`), and `σ` is one unbeatable strategy
    for every goal `G'` that holds wherever a play of `σ` reaches `G`. -/
theorem UnbeatableBy.sound {apps : Apps E} {p : Participant} {T : Threat E p}
    {σ : Strategy E p} {G : NetworkState E p → Prop} {net : NetworkState E p}
    (h : UnbeatableBy apps T σ G net) :
    (∃ n, Run apps T σ net n ∧ G n) ∧
    ∀ G' : NetworkState E p → Prop, (∀ n, Run apps T σ net n → G n → G' n) →
      Unbeatable apps T G' net := by
  induction h with
  | done hg => exact ⟨⟨_, .refl, hg⟩, fun _ hG' => .done (hG' _ .refl hg)⟩
  | move hf _ ih =>
    obtain ⟨n', hr⟩ := Threat.Round.exists T hf
    obtain ⟨n, hrun, hg⟩ := (ih n' hr).1
    exact ⟨⟨n, hrun.cons hr, hg⟩, fun G' hG' => .move _ trivial hf fun n1 hr1 =>
      (ih n1 hr1).2 G' fun n hrun hg => hG' n (hrun.cons hr1) hg⟩

/-- Nitro:480-481: "A channel χ is funded for participant A with x coins, if A
    has an unbeatable strategy for obtaining a state where χ is directly
    funded with x coins." -/
def FundedFor (apps : Apps E) {p : Participant} (T : Threat E p) (c : FixedPart) (x : Coins)
    (net : NetworkState E p) : Prop :=
  Unbeatable apps T (fun net' => net'.chain.DirectlyFundedWith c x) net

/-- `p` has an unbeatable strategy, with moves in `allowed`, for a balance of
    at least `x` at address `a`. -/
def CanObtainIn (apps : Apps E) {p : Participant} (T : Threat E p)
    (allowed : HonestMove E → Prop) (a : Address E) (x : Coins) (net : NetworkState E p) : Prop :=
  UnbeatableIn apps T allowed (fun net' => x ≤ net'.chain.balances.get a) net

/-- `CanObtainIn` with every honest move allowed. -/
def CanObtain (apps : Apps E) {p : Participant} (T : Threat E p) (a : Address E) (x : Coins)
    (net : NetworkState E p) : Prop :=
  CanObtainIn apps T (fun _ => True) a x net

/-- Nitro:482-484: "The value for participant A of a network state net is the
    maximum x for which A has an unbeatable strategy for obtaining a state
    where the balance of A's address in the adjudicator is x coins." The
    address is the external destination `d` (
    destinations are not participants). -/
def ValueIn (apps : Apps E) {p : Participant} (T : Threat E p) (allowed : HonestMove E → Prop)
    (d : E) (net : NetworkState E p) (x : Coins) : Prop :=
  CanObtainIn apps T allowed (.external d) x net ∧
  ∀ y, CanObtainIn apps T allowed (.external d) y net → y ≤ x

/-- `ValueIn` with every honest move allowed. -/
def Value (apps : Apps E) {p : Participant} (T : Threat E p) (d : E) (net : NetworkState E p)
    (x : Coins) : Prop :=
  ValueIn apps T (fun _ => True) d net x

/-- A family of network states, one per participant. Nitro:632-633: "the outcome
    of a channel is finalizable by all its participants". -/
def Views (E : Type) := ∀ p : Participant, NetworkState E p

/-- The views agree: they share one chain, a state `p` sends reaches its
    channel's other participants (the network
    is synchronous by construction, `State.recipients`), and a signature
    of `q` that `p` received is on a state `q` sent (SATP:168). The
    asynchronous system — where sending and delivery are separate steps,
    so a sent state need not yet have reached its recipients — is future
    work; this file models only the synchronous one. -/
def Views.Consistent (v : Views E) : Prop :=
  (∀ p q, (v p).chain = (v q).chain) ∧
  (∀ p, ∀ ss ∈ (v p).sent, ∀ q ∈ ss.state.recipients p, ss ∈ (v q).received) ∧
  (∀ p q, p ≠ q → ∀ r ∈ (v p).received, q ∈ r.signers → ∃ s ∈ (v q).sent, s.state = r.state)

/-- A family of threats, one per participant, and their assumptions. -/
structure Threats (E : Type) [DecidableEq E] (apps : Apps E) where
  T : ∀ p : Participant, Threat E p
  ok : ∀ p, Assumptions apps p (T p)

/-- Nitro:632-633: "In the special case where the outcome of a channel is
    finalizable by all its participants, we say that the outcome is
    universally finalizable." -/
def UniversallyFinalizable (apps : Apps E) (Ts : Threats E apps) (v : Views E) (c : FixedPart)
    (Ω : Outcome E) : Prop :=
  ∀ p ∈ c.participants, Finalizable apps (Ts.T p) c Ω (v p)

/-- Nitro:635-636: "After the first n states have been broadcast. In this state,
    we say the channel is at the funding point." Each participant holds the
    first `n` states, each signed by its mover, with outcome `Ω`, and no
    participant has signed any later state. -/
def AtFundingPoint (v : Views E) (c : FixedPart) (Ω : Outcome E) : Prop :=
  (∀ p ∈ c.participants, ∀ k, k < c.n →
    ∃ ss, (v p).Holds ss ∧ ss.state.channel = c ∧ ss.state.turnNum = k ∧
      ss.state.outcome = Ω ∧ ss.state.isFinal = false ∧ ss.ByMover) ∧
  (∀ p ∈ c.participants, ∀ ss ∈ (v p).sent, ss.state.channel = c → ss.state.turnNum < c.n)

/-- Nitro:637-638: "When a single conclusion proof is known to each participant.
    In this state, we say the channel is in the concluded state." -/
def Concluded (v : Views E) (c : FixedPart) (Ω : Outcome E) : Prop :=
  ∀ p ∈ c.participants, ∃ ss, (v p).Holds ss ∧ ConclusionProof c ss ∧ ss.state.outcome = Ω



omit [DecidableEq E] in
/-- D7: a received signed state is held as it
    is, its voucher signatures (SATP:630-637, SATP:703) travelling with it
    (`NetworkState.Holds`'s second clause). -/
theorem holds_of_mem_received {p : Participant} {net : NetworkState E p} {ss : SignedState E}
    (h : ss ∈ net.received) : net.Holds ss :=
  ⟨fun _ hq => .inr ⟨ss, h, rfl, hq⟩, fun _ hv _ _ => .inr ⟨ss, h, hv⟩⟩

end ArmadaLean.Nitro
