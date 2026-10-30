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

  Time bounds per pending action (operator ruling 2026-10-29,
  `armada-laconic/labbook/2026-10-29-machine-types-for-approval.md`, "Time
  bounds per pending action"). The earlier game bounded the adversary's
  clock advance per honest MOVE: a strategy needing two on-chain calls spent
  two rounds, and the second call could land almost `2 * ε` after the round
  started (`aln-c03`'s finding). Lamport's explicit-time form fixes this:
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
    sent, or a participant who signed a received state that carries the
    voucher. -/
def NetworkState.Holds {p : Participant} (net : NetworkState E p) (ss : SignedState E) : Prop :=
  (∀ q ∈ ss.signers,
    (q = p ∧ ∃ s ∈ net.sent, s.state = ss.state) ∨
    (∃ r ∈ net.received, r.state = ss.state ∧ q ∈ r.signers)) ∧
  ∀ v, ss.state.voucher? = some v → ∀ q ∈ v.signers,
    (q = p ∧ ∃ s ∈ net.sent, s.state.voucher? = some v) ∨
    (∃ r ∈ net.received, r.state.voucher? = some v ∧ q ∈ r.signers)

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
    and every goal vacuously "unbeatable"; soundness finding, this ruling's
    own review), and every proof state `op` submits is one `p` holds. -/
def Op.HonestFeasible {p : Participant} (net : NetworkState E p) : Op E → Prop
  | .deposit .. => False
  | .tick .. => False
  | op => ∀ ss ∈ op.proofStates, net.Holds ss

/-- A reaction is feasible when every one of its calls is. -/
def Reaction.Feasible {p : Participant} (net : NetworkState E p) (r : Reaction E) : Prop :=
  ∀ op ∈ r.calls, op.HonestFeasible net

/-- The honest participant may play a reaction only when every one of its
    calls is feasible; `wait` is always feasible. -/
def HonestMove.Feasible {p : Participant} (net : NetworkState E p) : HonestMove E → Prop
  | .react r => r.Feasible net
  | .wait _ => True

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
  simp [NetworkState.applyAdv, h]

/-- `applyAdv` of an on that fails: nothing changes. -/
@[simp] theorem NetworkState.applyAdv_chain_none (apps : Apps E) {p : Participant}
    {net : NetworkState E p} {caller : Participant} {op : Op E}
    (h : net.chain.apply apps caller op = none) :
    net.applyAdv apps (.chain caller op) = net := by
  simp [NetworkState.applyAdv, h]

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
  simp [NetworkState.applyAdv, h]

/-- `applyAdv` of `p`'s own pending call landing, when it fails. -/
@[simp] theorem NetworkState.applyAdv_land_none (apps : Apps E) {p : Participant}
    {net : NetworkState E p} {op : Op E}
    (h : net.chain.apply apps p op = none) :
    net.applyAdv apps (.land op) = net := by
  simp [NetworkState.applyAdv, h]

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

/-- One round's adversary play while `p`'s reaction, issued at the round's
    own start time `t`, still has `pending` calls unlanded (Lamport's
    explicit-time form, CHARME 2005, quoted in this file's header). Three
    kinds of step: `land` takes one call out of `pending` — chosen anywhere
    among the adversary's own moves, in any order (front-running); `tick` is
    disabled once it would push the clock past `t + T.ε` while any call is
    still pending — the one new constraint this ruling adds, read literally
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

/-- One round: `p`'s move `m`, issued at `net`'s clock, has every one of its
    calls landed (`Threat.RoundSeq`), and the round itself ends before
    `t + T.ε` has passed (Nitro:537-539, "before time t + ε") — the same
    bound `Threat.Round` always had, now read against the round's start
    rather than against a single call in isolation. `Threat.Round.single`
    shows the one-call case is exactly the old bound. -/
def Threat.Round (apps : Apps E) {p : Participant} (T : Threat E p) (m : HonestMove E)
    (net net' : NetworkState E p) : Prop :=
  Threat.RoundSeq apps T net.chain.now m.calls net net' ∧
  net'.chain.now < net.chain.now + T.ε

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

omit [DecidableEq E] in
@[simp] theorem HonestMove.Feasible_chain {p : Participant} (net : NetworkState E p) (op : Op E) :
    (HonestMove.chain op).Feasible net ↔ op.HonestFeasible net := by
  simp [HonestMove.Feasible, HonestMove.chain, Reaction.Feasible, Reaction.one]

omit [DecidableEq E] in
@[simp] theorem HonestMove.Feasible_send {p : Participant} (net : NetworkState E p) (st : State E) :
    (HonestMove.send st).Feasible net := by
  simp [HonestMove.Feasible, HonestMove.send, Reaction.Feasible]

omit [DecidableEq E] in
@[simp] theorem NetworkState.applyHonest_chain {p : Participant} (net : NetworkState E p)
    (op : Op E) : net.applyHonest (HonestMove.chain op) = net := by
  simp [NetworkState.applyHonest, HonestMove.chain, Reaction.one]

omit [DecidableEq E] in
@[simp] theorem NetworkState.applyHonest_send {p : Participant} (net : NetworkState E p)
    (st : State E) : net.applyHonest (HonestMove.send st) = { net with sent := ⟨st, [p]⟩ :: net.sent } := by
  simp [NetworkState.applyHonest, HonestMove.send]

/-- One call always peels off a `RoundSeq` as the LAST pending-clearing
    step: `[op]` has only one way to split, so every `land` step on
    `pending = [op]` consumes it whole, leaving `[]`. Stated over fresh
    state names (not the caller's), so `induction` builds the right
    motive. -/
theorem Threat.RoundSeq.peel_one {apps : Apps E} {p : Participant} {T : Threat E p} {t : Time}
    (op : Op E) (n0 n2 : NetworkState E p) (hseq : Threat.RoundSeq apps T t [op] n0 n2) :
    ∃ n1, Threat.RoundSeq apps T t [] n0 n1 ∧
      Threat.RoundSeq apps T t [] (n1.applyAdv apps (.land op)) n2 := by
  generalize hp : ([op] : List (Op E)) = pending at hseq
  induction hseq with
  | nil => cases hp
  | @land pending n net' op' l1 l2 hsplit hrest ih =>
    cases hp
    rcases l1 with _ | ⟨a, l1⟩
    · rcases l2 with _ | ⟨b, l2⟩
      · simp only [List.nil_append, List.cons.injEq] at hsplit
        obtain ⟨heq, -⟩ := hsplit
        subst heq
        exact ⟨n, Threat.RoundSeq.nil, hrest⟩
      · simp at hsplit
    · simp at hsplit
  | tick hfeas hgate hrest ih =>
    obtain ⟨n1, h1, h2⟩ := ih hp
    refine ⟨n1, Threat.RoundSeq.tick hfeas (Or.inr ?_) h1, h2⟩
    rcases hgate with h | h
    · cases hp.trans h
    · exact h
  | other hfeas hnotick hnoland hrest ih =>
    obtain ⟨n1, h1, h2⟩ := ih hp
    exact ⟨n1, Threat.RoundSeq.other hfeas hnotick hnoland h1, h2⟩


/-- Two calls peel off a `RoundSeq` one at a time, in whichever order the
    adversary front-runs them (Nitro:540-542): `pending = [opA, opB]` splits
    at a `land` step either on `opA` (leaving `[opB]` still pending) or on
    `opB` (leaving `[opA]`), with ordinary adversary play (`tick`/`other`)
    before that first `land`, exactly as `peel_one`'s singleton case.
    `peel_one`, applied to the returned singleton `RoundSeq`, splits the
    rest into its own ordinary-play-then-land shape.
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
  generalize hp : ([opA, opB] : List (Op E)) = pending at hseq
  induction hseq with
  | nil => cases hp
  | @land pending n net' op l1 l2 hsplit hrest ih =>
    cases hp
    rcases l1 with _ | ⟨a, l1⟩
    · rcases l2 with _ | ⟨b, l2⟩
      · simp at hsplit
      · rcases l2 with _ | ⟨c, l2⟩
        · simp only [List.nil_append, List.cons.injEq] at hsplit
          obtain ⟨hoA, hoB, -⟩ := hsplit
          subst hoA; subst hoB
          exact Or.inl ⟨n, Threat.RoundSeq.nil, hrest⟩
        · simp at hsplit
    · rcases l1 with _ | ⟨a1, l1⟩
      · rcases l2 with _ | ⟨c, l2⟩
        · simp only [List.cons_append, List.nil_append, List.cons.injEq] at hsplit
          obtain ⟨haA, hoB, -⟩ := hsplit
          subst haA; subst hoB
          exact Or.inr ⟨n, Threat.RoundSeq.nil, hrest⟩
        · simp at hsplit
      · simp at hsplit
  | tick hfeas hgate hrest ih =>
    rcases ih hp with ⟨n1, h1, h2⟩ | ⟨n1, h1, h2⟩
    · refine Or.inl ⟨n1, Threat.RoundSeq.tick hfeas (Or.inr ?_) h1, h2⟩
      rcases hgate with h | h
      · cases hp.trans h
      · exact h
    · refine Or.inr ⟨n1, Threat.RoundSeq.tick hfeas (Or.inr ?_) h1, h2⟩
      rcases hgate with h | h
      · cases hp.trans h
      · exact h
  | other hfeas hnotick hnoland hrest ih =>
    rcases ih hp with ⟨n1, h1, h2⟩ | ⟨n1, h1, h2⟩
    · exact Or.inl ⟨n1, Threat.RoundSeq.other hfeas hnotick hnoland h1, h2⟩
    · exact Or.inr ⟨n1, Threat.RoundSeq.other hfeas hnotick hnoland h1, h2⟩
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
    (soundness finding, this ruling's own review). With the clock
    unmoved, the round's own bound (`net'.chain.now < net.chain.now +
    T.ε`) is `T.ε_pos`. -/
theorem Threat.Round.exists {apps : Apps E} {p : Participant} (T : Threat E p)
    {m : HonestMove E} {net : NetworkState E p} (hfeas : m.Feasible net) :
    ∃ net', T.Round apps m net net' := by
  have hnotick : ∀ op ∈ m.calls, ∀ dt, op ≠ Op.tick dt := by
    cases m with
    | react r =>
      intro op hop dt heq
      have := hfeas op hop
      rw [heq] at this
      exact this
    | wait dt' => intro op hop; simp [HonestMove.calls] at hop
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
  | move {net} (m : HonestMove E) : allowed m → m.Feasible net →
      (∀ net', T.Round apps m net net' →
        UnbeatableIn apps T allowed G (net'.applyHonest m)) →
      UnbeatableIn apps T allowed G net

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

/-- Nitro:641-644: `p` "has a strategy to prevent" `G`: a strategy whose
    every move is feasible keeps every state of every play outside `G`,
    within the rounds too. -/
def Prevents (apps : Apps E) {p : Participant} (T : Threat E p)
    (G : NetworkState E p → Prop) (net : NetworkState E p) : Prop :=
  ∃ σ : Strategy E p, (∀ n, (σ n).Feasible n) ∧
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
    address is the external destination `d` (operator ruling 2026-10-27:
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
    channel's other participants (operator ruling 2026-10-29: the network
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

end ArmadaLean.Nitro
