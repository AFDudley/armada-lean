/-
  Nitro protocol specification: reachable network states. Operator ruling
  2026-10-29 (`labbook/2026-10-29-nitro-reachability-ruling.md`): the
  Liveness theorems assume a reachable network state, "views reachable from
  a genesis network (the genesis chain, empty sent and received lists) by
  honest moves and adversary rounds". The 2026-10-29 "Generic state:
  `Machine` and `System`" addendum: network reachability is the composed
  machine's `Machine.Reachable`, not a separate predicate. This file states
  the network game as a `Machine` and connects it to `Adjudicator.lean`'s
  existing chain-only `Reachable`.

  Explicit-time game (operator ruling 2026-10-29, "Time bounds per pending
  action", `Strategy.lean`'s header): a reaction's calls are no longer
  applied by `NetworkState.applyHonest`/`Network.applyHonest` — they land
  separately, one at a time, each gated only by its own feasibility at the
  moment it lands (`HonestFeasible`), not by which reaction first issued it.
  This is a sound over-approximation for bare reachability (every call that
  could ever legally land is reachable), the same relaxation a fuller
  `Threat.Round`-respecting reachability would refine; no Liveness theorem
  needs the refinement, only the game (`UnbeatableIn`) does.
-/
import ArmadaLean.Machine
import ArmadaLean.Nitro.Strategy
import ArmadaLean.Nitro.Lemmas

namespace ArmadaLean.Nitro

variable {E : Type} [DecidableEq E]

/-- An honest move (`NetworkState.applyHonest`) never touches the chain: a
    reaction's sends only ever touch `sent`, and its calls land separately
    (`.land`, below), not here. -/
theorem NetworkState.applyHonest_chain_reachable {apps : Apps E} {p : Participant}
    (net : NetworkState E p) (m : HonestMove E) (hr : Reachable apps net.chain) :
    Reachable apps (net.applyHonest m).chain := by
  cases m with
  | react r => simpa [NetworkState.applyHonest] using hr
  | wait dt =>
    simp only [NetworkState.applyHonest]
    have happly : net.chain.apply apps p (.tick dt) = some (net.chain.tick dt) := rfl
    exact hr.tail (Step.mk p (.tick dt) net.chain (net.chain.tick dt) happly)

/-- An adversary move (`NetworkState.applyAdv`) never changes the chain
    except through a successful `Adjudicator.apply`, for the same reason as
    `NetworkState.applyHonest_chain_reachable`. `deliver` never touches the
    chain; `land` applies with caller `p`, the same shape as `chain`. -/
theorem NetworkState.applyAdv_chain_reachable {apps : Apps E} {p : Participant}
    (net : NetworkState E p) (m : AdvMove E) (hr : Reachable apps net.chain) :
    Reachable apps (net.applyAdv apps m).chain := by
  cases m with
  | chain caller op =>
    simp only [NetworkState.applyAdv]
    cases h : net.chain.apply apps caller op with
    | none => exact hr
    | some s' => exact hr.tail (Step.mk caller op net.chain s' h)
  | deliver ss => simpa [NetworkState.applyAdv] using hr
  | tick dt =>
    simp only [NetworkState.applyAdv]
    have happly : net.chain.apply apps p (.tick dt) = some (net.chain.tick dt) := rfl
    exact hr.tail (Step.mk p (.tick dt) net.chain (net.chain.tick dt) happly)
  | land op =>
    simp only [NetworkState.applyAdv]
    cases h : net.chain.apply apps p op with
    | none => exact hr
    | some s' => exact hr.tail (Step.mk p op net.chain s' h)

/-- One successful on-chain step leaves a virtual channel's balance at
    zero, given it started at zero. `Adjudicator.deposit` refuses a
    virtual-kind channel address (`Adjudicator.deposit_some`); a
    `transfer`'s paid destination must be `fundable`, which excludes a
    virtual channel (`Address.fundable`), and its source channel must be a
    ledger channel, so it cannot be the virtual `c` either
    (`Adjudicator.transfer_some`); `reclaim`, `challenge`, `checkpoint`,
    `conclude` and `tick` never write `balances`
    (`Adjudicator.setStatus_balances`, `Adjudicator.tick_balances`). -/
theorem balances_virtual_zero_step {apps : Apps E} {s s' : Adjudicator E} {caller : Participant}
    {op : Op E} {c : FixedPart} (hk : c.kind = .virtual)
    (ih : s.balances.get (.channel c) = 0) (h : s.apply apps caller op = some s') :
    s'.balances.get (.channel c) = 0 := by
  cases op with
  | deposit a e x =>
    obtain ⟨⟨c', hac', hck'⟩, -, hb, -, -, -⟩ := Adjudicator.deposit_some h
    have hne : (Address.channel c : Address E) ≠ a := by
      rw [hac']
      intro hcc
      injection hcc with hcc'
      have hkeq : c.kind = c'.kind := congrArg FixedPart.kind hcc'
      rw [hk, hck'] at hkeq
      cases hkeq
    rw [hb, Balances.get_add, if_neg hne]
    exact ih
  | transfer a b =>
    obtain ⟨o, amt, x, -, hfind, -, hb, -, -, -, hak, hbf⟩ := Adjudicator.transfer_some h
    have hbc : (Address.channel c : Address E) ≠ b := by
      rintro rfl
      simp [Address.fundable, hk] at hbf
    have hac : (Address.channel c : Address E) ≠ a.address := by
      rw [FixedPart.address_eq]
      intro hcc
      injection hcc with hcc'
      have hkeq : c.kind = a.kind := congrArg FixedPart.kind hcc'
      rw [hk, hak] at hkeq
      cases hkeq
    rw [hb, Balances.get_sub, if_neg hac, Balances.get_add, if_neg hbc]
    exact ih
  | reclaim l v =>
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, rfl, _, _⟩ := Adjudicator.reclaim_some h
    simpa using ih
  | challenge c' proof candidate =>
    obtain ⟨_, rfl⟩ := Adjudicator.challenge_some h
    simpa using ih
  | checkpoint c' proof candidate =>
    obtain ⟨_, rfl⟩ := Adjudicator.checkpoint_some h
    simpa using ih
  | conclude c' ss =>
    obtain ⟨_, rfl⟩ := Adjudicator.conclude_some h
    simpa using ih
  | tick dt =>
    simp at h
    subst h
    simpa using ih

/-- **A reachable chain holds no coins in a virtual-kind channel.** Operator
    ruling 2026-10-29: the counterexamples to `directly_funded_pays`,
    `finalizable_funded_pays` and `ledger_partial_withdrawal` each put coins
    in a virtual-kind channel, which `deposit` and `transfer` refuse
    (`Adjudicator.deposit`, `Adjudicator.transfer`,
    `Adjudicator.lean:100-152`). Genesis holds no balances at all
    (`Adjudicator.genesis`, `Balances.get` on `[]`); every step keeps a
    virtual channel's balance at zero (`balances_virtual_zero_step`). -/
theorem Reachable.balances_virtual_zero {apps : Apps E} {s : Adjudicator E}
    (hr : Reachable apps s) (c : FixedPart) (hk : c.kind = .virtual) :
    s.balances.get (.channel c) = 0 := by
  induction hr with
  | refl => rfl
  | tail _ hstep ih =>
    obtain ⟨caller, op, _, _, happ⟩ := hstep
    exact balances_virtual_zero_step hk ih happ

end ArmadaLean.Nitro

open ArmadaLean.Nitro

variable {E : Type} [DecidableEq E]

/-- `p`'s own machine: from the empty state (`Adjudicator.genesis`, empty
    `sent` and `received`, Nitro:446-454), one of `p`'s own feasible honest
    moves (`NetworkState.applyHonest`, `HonestMove.Feasible`), `p` landing
    one of its own currently-feasible calls directly (`land`, the
    explicit-time game's two-phase issue/land split collapsed back to one
    step, sound for bare reachability — this file's header), or one
    feasible move of the adversary `T` (`NetworkState.applyAdv`,
    `Threat.feasible`). Declared at the root, not inside `ArmadaLean.Nitro`
    (which already holds `NetworkState`, `Threat`, ...), so its name is
    `Nitro.participant`, not `ArmadaLean.Nitro.Nitro.participant`; this
    mirrors `Pool.machine` (`PoolMachine.lean`), itself declared outside
    `Pool.lean`'s (namespace-free) declarations. -/
def Nitro.participant (apps : Apps E) {p : Participant} (T : Threat E p) :
    Machine (NetworkState E p) where
  init := fun net => net = ⟨Adjudicator.genesis, [], []⟩
  step := fun net net' =>
    (∃ m : HonestMove E, m.Feasible net ∧ net' = net.applyHonest m) ∨
    (∃ op : Op E, op.HonestFeasible net ∧ net' = net.applyAdv apps (.land op)) ∨
    (∃ m : AdvMove E, T.feasible net m ∧ net' = net.applyAdv apps m)

/-- `Nitro.chain apps`: the chain alone as a `Machine`, from
    `Adjudicator.genesis` by one `Step` at a time. -/
def Nitro.chain (apps : Apps E) : Machine (Adjudicator E) where
  init := fun s => s = Adjudicator.genesis
  step := Step apps

/-- `Nitro.chain apps`'s `Machine.Reachable` is exactly `Adjudicator.lean`'s
    `Reachable apps` (`Adjudicator.lean:308`): both are the empty state
    closed under `Step apps` by `Relation.ReflTransGen`. -/
theorem Nitro.chain_reachable_iff {apps : Apps E} {s : Adjudicator E} :
    (Nitro.chain apps).Reachable s ↔ Reachable apps s := by
  constructor
  · rintro ⟨s₀, rfl, hsteps⟩
    exact hsteps
  · intro hr
    exact ⟨Adjudicator.genesis, rfl, hr⟩

/-- **The chain of a reachable network state is reachable.** By
    `Machine.invariant` over `Nitro.participant apps T`, with
    `NetworkState.applyHonest_chain_reachable` /
    `NetworkState.applyAdv_chain_reachable` for the step case (the `land`
    branch is `applyAdv_chain_reachable`'s own `land` case) and
    `Relation.ReflTransGen.refl` for the (unique) initial state. -/
theorem Nitro.participant_chain_reachable {apps : Apps E} {p : Participant} {T : Threat E p}
    {net : NetworkState E p} (h : (Nitro.participant apps T).Reachable net) :
    Reachable apps net.chain := by
  refine Machine.invariant (Nitro.participant apps T) (P := fun net => Reachable apps net.chain)
    ?_ ?_ net h
  · intro net hinit
    rw [hinit]
    exact Relation.ReflTransGen.refl
  · intro net net' hP hstep
    rcases hstep with ⟨m, -, rfl⟩ | ⟨op, -, rfl⟩ | ⟨m, -, rfl⟩
    · exact NetworkState.applyHonest_chain_reachable net m hP
    · exact NetworkState.applyAdv_chain_reachable net (.land op) hP
    · exact NetworkState.applyAdv_chain_reachable net m hP

/-- A full network state: ONE shared chain, and each participant's own
    `sent`/`received`. Coordinator finding 2026-10-29: `Machine.interleave`
    over one `Nitro.participant` machine per participant is wrong, because
    `interleave` composes machines with NO shared state
    (`Machine.interleave`'s own doc comment), and the chain IS shared — a
    step that moves one participant's own `NetworkState` copy, under
    `interleave`, leaves every other participant's chain copy where it
    was, so chains diverge across an interleaved run. `Network` fixes this
    the Stratum 1.2 way (illegal state unrepresentable, `docs/process.md`):
    one `chain` field, not one per participant, so two views can never
    disagree on it by construction (`Network.views_chain_eq`). -/
structure Network (E : Type) where
  chain : Adjudicator E
  sent : Participant → List (SignedState E)
  received : Participant → List (SignedState E)

/-- `p`'s view of a `Network`: exactly `Strategy.lean`'s `NetworkState`,
    read off the shared chain and `p`'s own lists. -/
def Network.view (n : Network E) (p : Participant) : NetworkState E p :=
  ⟨n.chain, n.received p, n.sent p⟩

/-- The family of views `Views.Consistent` and every multi-view Liveness
    theorem read. -/
def Network.views (n : Network E) : Views E := n.view

omit [DecidableEq E] in
/-- Every participant's view of a `Network` shares the one chain, by
    construction — no reachability needed, unlike the two other
    `Views.Consistent` conjuncts below. -/
theorem Network.views_chain_eq (n : Network E) (p q : Participant) :
    (n.views p).chain = (n.views q).chain := rfl

/-- A signed state every one of its claimed signers genuinely sent, and
    the same for any voucher it carries — the same shape as
    `SignedState.SignedIn` (`Adjudicator.lean:316`, used by
    `ReachableSigned`), here read against `n`'s own `sent` record instead
    of an abstract `signed` list. Gates `Network.land`'s broadcast and the
    old `Nitro.network`'s `.deliver`: see those definitions' doc comments
    for why the per-participant model alone does not already enforce
    this. -/
def Network.Sendable (n : Network E) (ss : SignedState E) : Prop :=
  (∀ q ∈ ss.signers, ∃ s ∈ n.sent q, s.state = ss.state) ∧
  ∀ v, ss.state.voucher? = some v → ∀ q ∈ v.signers, ∃ s ∈ n.sent q, s.state.voucher? = some v

/-- A state's voucher, if any, is only sent by participants who already
    hold a matching-voucher state of their own. Gates `Nitro.network`'s
    honest `.react`: `Network.Sendable`'s own first conjunct cannot gate a
    first send of `st` (`p`'s own `sent` does not yet hold it), but every
    recipient's `Unforged` check (`Strategy.lean`) only reads its own
    alleged signature — vacuous here, since the delivered entry's sole
    top-level signer is `p` itself, never the recipient — and `st`'s
    voucher's signers, which this clause covers exactly. -/
def Network.VoucherSendable (n : Network E) (st : State E) : Prop :=
  ∀ v, st.voucher? = some v → ∀ q ∈ v.signers, ∃ s ∈ n.sent q, s.state.voucher? = some v

/-- One honest move of `p`, applied to the whole `Network`
    (`NetworkState.applyHonest`, read from `p`'s view): a reaction's sends
    reach the sender's own `sent`, and, in the same step (operator ruling
    2026-10-29, synchronous network), every recipient's `received`
    (`State.recipients`, `Channel.lean`) — one shot, not a fold, so a
    recipient `q`'s one new batch of entries is exactly the sends `q`
    actually receives, `(r.sends.filter (q ∈ ·.recipients p)).map _`.
    A reaction's calls do not touch the chain here — they land
    separately, one at a time, through `Network.land` (the explicit-time
    game's pending calls, `Strategy.lean`'s header). `wait` still moves
    the clock directly, `p`'s own move. -/
def Network.applyHonest (n : Network E) (p : Participant) (m : HonestMove E) : Network E :=
  match m with
  | .react r =>
    { n with
      sent := fun q =>
        if q = p then r.sends.map (fun st => (⟨st, [p]⟩ : SignedState E)) ++ n.sent q
        else n.sent q
      received := fun q =>
        (r.sends.filter (fun st => decide (q ∈ st.recipients p))).map
          (fun st => (⟨st, [p]⟩ : SignedState E)) ++ n.received q }
  | .wait dt => { n with chain := n.chain.tick dt }

omit [DecidableEq E] in
@[simp] theorem Network.applyHonest_react_chain (n : Network E) (p : Participant) (r : Reaction E) :
    (Network.applyHonest n p (.react r)).chain = n.chain := rfl

omit [DecidableEq E] in
theorem Network.applyHonest_react_sent (n : Network E) (p : Participant) (r : Reaction E)
    (q : Participant) : (Network.applyHonest n p (.react r)).sent q =
      if q = p then r.sends.map (fun st => (⟨st, [p]⟩ : SignedState E)) ++ n.sent q
      else n.sent q := rfl

omit [DecidableEq E] in
theorem Network.applyHonest_react_received (n : Network E) (p : Participant) (r : Reaction E)
    (q : Participant) : (Network.applyHonest n p (.react r)).received q =
      (r.sends.filter (fun st => decide (q ∈ st.recipients p))).map
        (fun st => (⟨st, [p]⟩ : SignedState E)) ++ n.received q := rfl

/-- `p` never receives its own send: `State.recipients` excludes `p` by
    construction, so the filter above is always empty at `q = p`. -/
theorem Network.applyHonest_react_received_self (n : Network E) (p : Participant) (r : Reaction E) :
    (Network.applyHonest n p (.react r)).received p = n.received p := by
  rw [Network.applyHonest_react_received]
  have hempty : r.sends.filter (fun st => decide (p ∈ st.recipients p)) = [] := by
    rw [List.filter_eq_nil_iff]
    intro st _
    simp [State.recipients, List.mem_filter]
  rw [hempty]
  rfl

/-- `p` lands one of its own currently-feasible calls, applied to the whole
    `Network`: public, the same broadcast shape as `.chain` always had
    (D9 repair, `docs/nitro-repair-2026-10-27.md`) — every participant's
    `received` gains `op.proofStates`, since an on-chain call is public.
    `p`'s own entry is redundant (`HonestFeasible` already requires `p` to
    hold every proof state before landing) but harmless, and keeps this
    the same shape as `NetworkState.applyAdv`'s own `.land` case (always
    self-referential there, so it never excludes the landing participant
    either). A failed call changes nothing (ForceMove:685-686). -/
def Network.land (apps : Apps E) (n : Network E) (p : Participant) (op : Op E) : Network E :=
  match n.chain.apply apps p op with
  | some s' => { chain := s', sent := n.sent, received := fun q => op.proofStates ++ n.received q }
  | none => n

/-- One adversary move against `p`, applied to the whole `Network`
    (`NetworkState.applyAdv`, read from `p`'s view). `.deliver ss` reaches
    only `p`'s own `received`: the per-participant model alone does not
    forbid delivering a forged OTHER signer's claim
    (`Bounds.unforgeable`/`NetworkState.Unforged` bound only `p`'s own
    alleged signature, by design, `Strategy.lean`), so `Nitro.network`'s
    step additionally requires `Network.Sendable ss`. The caller rule
    (operator ruling 2026-10-29) excludes `.chain` and `.land` from the
    adversary's own moves at the `Nitro.network` step (below); this
    function still accepts them, for the single-view lemmas that reuse
    it with an explicit caller/landing participant. Operator ruling
    2026-10-29 (synchronous network): `.deliver` stays, on top of the
    now-synchronous `.send`/`.react`, for two cases the recipient-scoped
    broadcast cannot cover. First, a multi-signer state (`SignedState.ByAll`,
    `Strategy.lean`, e.g. a conclusion proof every participant has signed)
    needs an entry whose `signers` list names more than the one sender a
    send ever attaches. Second, an observer outside a channel
    (`late_observer_can_checkpoint`) is not a recipient of that channel's
    states (`State.recipients` excludes every non-participant by
    construction), so only `.deliver` reaches it. -/
def Network.applyAdv (apps : Apps E) (n : Network E) (p : Participant) (m : AdvMove E) :
    Network E :=
  match m with
  | .chain caller op =>
    match n.chain.apply apps caller op with
    | some s' => { chain := s', sent := n.sent, received := fun q => op.proofStates ++ n.received q }
    | none => n
  | .deliver ss => { n with received := fun q => if q = p then ss :: n.received q else n.received q }
  | .tick dt => { n with chain := n.chain.tick dt }
  | .land op => Network.land apps n p op

theorem Network.applyHonest_chain_reachable {apps : Apps E} (n : Network E) (p : Participant)
    (m : HonestMove E) (hr : Reachable apps n.chain) :
    Reachable apps (Network.applyHonest n p m).chain := by
  cases m with
  | react r => simpa using hr
  | wait dt =>
    simp only [Network.applyHonest]
    have happly : n.chain.apply apps p (.tick dt) = some (n.chain.tick dt) := rfl
    exact hr.tail (Step.mk p (.tick dt) n.chain (n.chain.tick dt) happly)

theorem Network.land_chain_reachable {apps : Apps E} (n : Network E) (p : Participant) (op : Op E)
    (hr : Reachable apps n.chain) : Reachable apps (Network.land apps n p op).chain := by
  simp only [Network.land]
  cases h : n.chain.apply apps p op with
  | none => exact hr
  | some s' => exact hr.tail (Step.mk p op n.chain s' h)

theorem Network.applyAdv_chain_reachable {apps : Apps E} (n : Network E) (p : Participant)
    (m : AdvMove E) (hr : Reachable apps n.chain) :
    Reachable apps (Network.applyAdv apps n p m).chain := by
  cases m with
  | chain caller op =>
    simp only [Network.applyAdv]
    cases h : n.chain.apply apps caller op with
    | none => exact hr
    | some s' => exact hr.tail (Step.mk caller op n.chain s' h)
  | deliver ss => simpa [Network.applyAdv] using hr
  | tick dt =>
    simp only [Network.applyAdv]
    have happly : n.chain.apply apps p (.tick dt) = some (n.chain.tick dt) := rfl
    exact hr.tail (Step.mk p (.tick dt) n.chain (n.chain.tick dt) happly)
  | land op => exact Network.land_chain_reachable n p op hr

/-- The network game: at each step, some participant `p` makes one of its
    own feasible honest moves (a reaction's sends only, calls land
    separately below), `p` lands one of its own currently-feasible calls
    (`Network.land`, gated by `Network.Sendable` on its proof states, the
    same public-broadcast fact the old `.chain` gate stated), or `p`'s own
    adversary `Ts.T p` makes one feasible `.deliver`/`.tick` move against
    `p`. `Network.Sendable` gates a `.deliver` and every landed call's
    proof states: SATP:168 "forging cryptographic signatures is
    infeasible" is a system-wide fact, already encoded on the chain side
    by `ReachableSigned`'s own hypothesis (`Adjudicator.lean`, `SignedStep`'s
    `hsig`); this is the same fact for the network's own `sent` record, so
    every signature a proof state carries is genuine, not only the acting
    view's own. The caller rule (operator ruling 2026-10-29, "Caller
    rule",
    `armada-laconic/labbook/2026-10-29-machine-types-for-approval.md`
    §"Result" item 3, read literally): "only q's own honest moves may
    submit an on-chain call with caller q" — for every participant, not
    only a channel's, and (explicit-time addendum) the same for landing:
    only `q`'s own call ever lands with caller `q`. An adversary move is
    never a `.chain` or `.land` move at all, so the adversary's moves are
    only `.deliver` and `.tick`. Operator ruling 2026-10-29:
    `ReachableViews` is `(Nitro.network apps Ts).Reachable`, not a separate
    predicate. A second gate, `Network.VoucherSendable`, covers the one
    part of `Network.Sendable` a first send cannot satisfy of itself (that
    definition's doc comment). -/
def Nitro.network (apps : Apps E) (Ts : Threats E apps) : Machine (Network E) where
  init := fun n => n = ⟨Adjudicator.genesis, fun _ => [], fun _ => []⟩
  step := fun n n' => ∃ p : Participant,
    (∃ m : HonestMove E, m.Feasible (n.view p) ∧
      (∀ r : Reaction E, m = .react r → ∀ st ∈ r.sends, n.VoucherSendable st) ∧
      n' = Network.applyHonest n p m) ∨
    (∃ op : Op E, op.HonestFeasible (n.view p) ∧
      (∀ ss ∈ op.proofStates, n.Sendable ss) ∧
      n' = Network.land apps n p op) ∨
    (∃ m : AdvMove E, (Ts.T p).feasible (n.view p) m ∧
      (∀ ss, m = .deliver ss → n.Sendable ss) ∧
      (∀ caller op, m ≠ .chain caller op) ∧ (∀ op, m ≠ .land op) ∧
      n' = Network.applyAdv apps n p m)

/-- **The chain of a reachable `Network` is reachable.** By
    `Machine.invariant`, using `Network.applyHonest_chain_reachable` /
    `Network.land_chain_reachable` / `Network.applyAdv_chain_reachable` for
    the step case. -/
theorem Nitro.network_chain_reachable {apps : Apps E} {Ts : Threats E apps} {n : Network E}
    (h : (Nitro.network apps Ts).Reachable n) : Reachable apps n.chain := by
  refine Machine.invariant (Nitro.network apps Ts) (P := fun n => Reachable apps n.chain) ?_ ?_ n h
  · intro n hinit
    rw [hinit]
    exact Relation.ReflTransGen.refl
  · intro n n' hP hstep
    obtain ⟨p, ⟨m, -, -, rfl⟩ | ⟨op, -, -, rfl⟩ | ⟨m, -, -, -, -, rfl⟩⟩ := hstep
    · exact Network.applyHonest_chain_reachable n p m hP
    · exact Network.land_chain_reachable n p op hP
    · exact Network.applyAdv_chain_reachable n p m hP

/-- **`Views.Consistent`'s third conjunct holds for every reachable
    `Network`.** A state `p` received that names `q` as a signer is a
    state `q` really sent. By `Machine.invariant`: at genesis every
    `received` is empty (vacuous); a step leaves `received` untouched
    (`wait`), touches only the mover's own `received` through a
    `Network.Sendable`-gated `.deliver` (whose statement is exactly this
    conjunct for the one new entry), broadcasts a landed call's
    `Network.Sendable`-gated proof states (same argument, for every new
    entry at once), or appends a `.react`'s one-shot recipient batch, each
    new entry's own signer `p₀` already known-genuine by `hP`. -/
theorem Nitro.network_views_signers {apps : Apps E} {Ts : Threats E apps} {n : Network E}
    (h : (Nitro.network apps Ts).Reachable n) :
    ∀ p q : Participant, p ≠ q → ∀ r ∈ (n.views p).received, q ∈ r.signers →
      ∃ s ∈ (n.views q).sent, s.state = r.state := by
  refine Machine.invariant (Nitro.network apps Ts)
    (P := fun n => ∀ p q : Participant, p ≠ q → ∀ r ∈ n.received p, q ∈ r.signers →
      ∃ s ∈ n.sent q, s.state = r.state) ?_ ?_ n h
  · intro n hinit p q hpq r hr
    rw [hinit] at hr
    simp at hr
  · intro n n' hP hstep p q hpq r hr hqr
    obtain ⟨p₀, ⟨m, -, -, rfl⟩ | ⟨op, -, hsgate, rfl⟩ | ⟨m, -, hdgate, hnochain, hnoland, rfl⟩⟩ :=
      hstep
    · cases m with
      | react rr =>
        rw [Network.applyHonest_react_received] at hr
        rw [List.mem_append] at hr
        rcases hr with hnew | hold
        · obtain ⟨st, hst, hseq⟩ := List.mem_map.mp hnew
          obtain ⟨hst', -⟩ := List.mem_filter.mp hst
          rw [← hseq] at hqr
          simp only [List.mem_singleton] at hqr
          refine ⟨⟨st, [p₀]⟩, ?_, by rw [← hseq]⟩
          rw [Network.applyHonest_react_sent, if_pos hqr]
          exact List.mem_append_left _ (List.mem_map.mpr ⟨st, hst', rfl⟩)
        · obtain ⟨s, hs, hseq⟩ := hP p q hpq r hold hqr
          refine ⟨s, ?_, hseq⟩
          rw [Network.applyHonest_react_sent]
          by_cases hqp0 : q = p₀
          · rw [if_pos hqp0]; exact List.mem_append_right _ hs
          · rw [if_neg hqp0]; exact hs
      | wait dt =>
        have hrecv : (Network.applyHonest n p₀ (.wait dt)).received p = n.received p := by
          simp [Network.applyHonest]
        have hsent : (Network.applyHonest n p₀ (.wait dt)).sent = n.sent := by
          simp [Network.applyHonest]
        rw [hrecv] at hr
        rw [hsent]
        exact hP p q hpq r hr hqr
    · cases hop : n.chain.apply apps p₀ op with
      | none =>
        have hsent : (Network.land apps n p₀ op).sent = n.sent := by
          simp [Network.land, hop]
        have hrecv : (Network.land apps n p₀ op).received p = n.received p := by
          simp [Network.land, hop]
        rw [hsent]
        rw [hrecv] at hr
        exact hP p q hpq r hr hqr
      | some s' =>
        have hsent : (Network.land apps n p₀ op).sent = n.sent := by
          simp [Network.land, hop]
        have hrecv : (Network.land apps n p₀ op).received p = op.proofStates ++ n.received p := by
          simp [Network.land, hop]
        rw [hsent]
        rw [hrecv] at hr
        rcases List.mem_append.mp hr with hnew | hold
        · exact (hsgate r hnew).1 q hqr
        · exact hP p q hpq r hold hqr
    · cases m with
      | chain caller op => exact absurd rfl (hnochain caller op)
      | deliver ss =>
        have hsent : (Network.applyAdv apps n p₀ (.deliver ss)).sent = n.sent := by
          simp [Network.applyAdv]
        have hrecv : (Network.applyAdv apps n p₀ (.deliver ss)).received p =
            if p = p₀ then ss :: n.received p else n.received p := by
          simp [Network.applyAdv]
        rw [hsent]
        rw [hrecv] at hr
        by_cases hpp0 : p = p₀
        · rw [if_pos hpp0] at hr
          rcases List.mem_cons.mp hr with rfl | hold
          · exact (hdgate r rfl).1 q hqr
          · exact hP p q hpq r hold hqr
        · rw [if_neg hpp0] at hr
          exact hP p q hpq r hr hqr
      | tick dt =>
        have hrecv : (Network.applyAdv apps n p₀ (.tick dt)).received p = n.received p := by
          simp [Network.applyAdv]
        have hsent : (Network.applyAdv apps n p₀ (.tick dt)).sent = n.sent := by
          simp [Network.applyAdv]
        rw [hrecv] at hr
        rw [hsent]
        exact hP p q hpq r hr hqr
      | land op => exact absurd rfl (hnoland op)

/-- Bigger `signed` lists only reach more: `SignedState.SignedIn` is
    monotone in `signed`, so a `SignedStep` for `signed` is also one for
    any `signed' ⊇ signed`, and `ReachableSigned` follows by induction. -/
theorem ReachableSigned.mono {apps : Apps E} {signed signed' : List (Participant × State E)}
    (hsub : signed ⊆ signed') {s : Adjudicator E} (h : ReachableSigned apps signed s) :
    ReachableSigned apps signed' s := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih =>
    obtain ⟨caller, op, _, _, hsig, happly⟩ := hstep
    refine ih.tail ⟨caller, op, _, _, ?_, happly⟩
    intro ss hss
    obtain ⟨h1, h2⟩ := hsig ss hss
    refine ⟨fun q hq => hsub (h1 q hq), fun v hv q hq => ?_⟩
    obtain ⟨st, hst, hv'⟩ := h2 v hv q hq
    exact ⟨st, hsub hst, hv'⟩

/-- **Every reachable `Network`'s chain is `ReachableSigned`**, for a
    signed-state record that exactly mirrors its own `sent`. `Participant`
    (`Address.lean`, a bare `Nat` wrapper) is infinite, so no single flat
    list can be "all of `n.sent`" at once; the existential below is the
    finite record one actual reachability derivation builds, carried along
    the same induction as `Nitro.network_views_signers`:
    `Network.Sendable`, gated on every landed call's proof states by
    `Nitro.network`'s step, is `SignedState.SignedIn` read against
    `n.sent` instead of `signed`, so each new chain step is a genuine
    `SignedStep`. -/
theorem Nitro.network_chain_reachableSigned {apps : Apps E} {Ts : Threats E apps} {n : Network E}
    (h : (Nitro.network apps Ts).Reachable n) :
    ∃ signed : List (Participant × State E),
      ReachableSigned apps signed n.chain ∧
      ∀ q st, (q, st) ∈ signed ↔ ∃ s ∈ n.sent q, s.state = st := by
  refine Machine.invariant (Nitro.network apps Ts)
    (P := fun n => ∃ signed : List (Participant × State E),
      ReachableSigned apps signed n.chain ∧
      ∀ q st, (q, st) ∈ signed ↔ ∃ s ∈ n.sent q, s.state = st) ?_ ?_ n h
  · intro n hinit
    refine ⟨[], ?_, ?_⟩
    · rw [hinit]; exact Relation.ReflTransGen.refl
    · intro q st; rw [hinit]; simp
  · intro n n' hP hstep
    obtain ⟨signed, hreach, hmirror⟩ := hP
    obtain ⟨p₀, ⟨m, -, -, rfl⟩ | ⟨op, -, hsgate, rfl⟩ | ⟨m, -, -, hnochain, hnoland, rfl⟩⟩ := hstep
    · cases m with
      | react rr =>
        refine ⟨rr.sends.map (fun st => (p₀, st)) ++ signed, ?_, ?_⟩
        · simpa using ReachableSigned.mono (fun x hx => List.mem_append_right _ hx) hreach
        · intro q st
          rw [Network.applyHonest_react_sent, List.mem_append, List.mem_map]
          by_cases hqp0 : q = p₀
          · simp only [if_pos hqp0, List.mem_append, List.mem_map]
            constructor
            · rintro (⟨st', hst', hseq⟩ | hmem)
              · rw [Prod.mk.injEq] at hseq
                exact ⟨⟨st', [p₀]⟩, Or.inl ⟨st', hst', rfl⟩, hseq.2⟩
              · obtain ⟨s, hs, hseq⟩ := (hmirror q st).mp hmem
                exact ⟨s, Or.inr hs, hseq⟩
            · rintro ⟨s, (⟨st', hst', hseq⟩ | hmem), hstate⟩
              · subst hseq
                exact Or.inl ⟨st', hst', by rw [Prod.mk.injEq]; exact ⟨hqp0.symm, hstate⟩⟩
              · exact Or.inr ((hmirror q st).mpr ⟨s, hmem, hstate⟩)
          · simp only [if_neg hqp0]
            constructor
            · rintro (⟨st', hst', hseq⟩ | hmem)
              · rw [Prod.mk.injEq] at hseq
                exact absurd hseq.1.symm hqp0
              · exact (hmirror q st).mp hmem
            · intro hmem
              exact Or.inr ((hmirror q st).mpr hmem)
      | wait dt =>
        have hc : (Network.applyHonest n p₀ (.wait dt)).chain = n.chain.tick dt := by
          simp [Network.applyHonest]
        have hs : (Network.applyHonest n p₀ (.wait dt)).sent = n.sent := by
          simp [Network.applyHonest]
        refine ⟨signed, ?_, by rw [hs]; exact hmirror⟩
        rw [hc]
        refine hreach.tail ⟨p₀, .tick dt, _, _, ?_, rfl⟩
        simp [Op.proofStates]
    · cases hop : n.chain.apply apps p₀ op with
      | none =>
        refine ⟨signed, ?_, ?_⟩
        · have hc : (Network.land apps n p₀ op).chain = n.chain := by simp [Network.land, hop]
          rw [hc]; exact hreach
        · have hs : (Network.land apps n p₀ op).sent = n.sent := by simp [Network.land, hop]
          rw [hs]; exact hmirror
      | some s' =>
        have hc : (Network.land apps n p₀ op).chain = s' := by simp [Network.land, hop]
        have hs : (Network.land apps n p₀ op).sent = n.sent := by simp [Network.land, hop]
        refine ⟨signed, ?_, by rw [hs]; exact hmirror⟩
        rw [hc]
        refine hreach.tail ⟨p₀, op, _, _, ?_, hop⟩
        intro ss hss
        obtain ⟨hsg, hvoucher⟩ := hsgate ss hss
        refine ⟨fun q' hq' => ?_, fun v hv q' hq' => ?_⟩
        · obtain ⟨s, hs', hseq⟩ := hsg q' hq'
          exact (hmirror q' ss.state).mpr ⟨s, hs', hseq⟩
        · obtain ⟨s, hs', hseq⟩ := hvoucher v hv q' hq'
          exact ⟨s.state, (hmirror q' s.state).mpr ⟨s, hs', rfl⟩, hseq⟩
    · cases m with
      | chain caller op => exact absurd rfl (hnochain caller op)
      | deliver ss =>
        have hc : (Network.applyAdv apps n p₀ (.deliver ss)).chain = n.chain := by
          simp [Network.applyAdv]
        have hs : (Network.applyAdv apps n p₀ (.deliver ss)).sent = n.sent := by
          simp [Network.applyAdv]
        exact ⟨signed, by rw [hc]; exact hreach, by rw [hs]; exact hmirror⟩
      | tick dt =>
        have hc : (Network.applyAdv apps n p₀ (.tick dt)).chain = n.chain.tick dt := by
          simp [Network.applyAdv]
        have hs : (Network.applyAdv apps n p₀ (.tick dt)).sent = n.sent := by
          simp [Network.applyAdv]
        refine ⟨signed, ?_, by rw [hs]; exact hmirror⟩
        rw [hc]
        refine hreach.tail ⟨p₀, .tick dt, _, _, ?_, rfl⟩
        simp [Op.proofStates]
      | land op => exact absurd rfl (hnoland op)

/-- **`Views.Consistent`'s second conjunct holds for every reachable
    `Network`.** Operator ruling 2026-10-29: the network is synchronous by
    construction, so a state `p` sends reaches its recipients in the same
    step (`Network.applyHonest`'s `.react` arm). By `Machine.invariant`: at
    genesis every `sent` is empty (vacuous); a step leaves `sent`
    untouched except an honest `.react`, which both appends to the
    sender's own `sent` and, in the same step, to every recipient's
    `received`; every other move only ever grows `received`, for any
    participant, never removes from it, so a state already delivered to
    one of its recipients stays delivered. -/
theorem Nitro.network_views_delivered {apps : Apps E} {Ts : Threats E apps} {n : Network E}
    (h : (Nitro.network apps Ts).Reachable n) :
    ∀ p, ∀ ss ∈ (n.views p).sent, ∀ q ∈ ss.state.recipients p, ss ∈ (n.views q).received := by
  refine Machine.invariant (Nitro.network apps Ts)
    (P := fun n => ∀ p, ∀ ss ∈ n.sent p, ∀ q ∈ ss.state.recipients p, ss ∈ n.received q)
    ?_ ?_ n h
  · intro n hinit p ss hss
    rw [hinit] at hss
    simp at hss
  · intro n n' hP hstep p ss hss q hq
    obtain ⟨p₀, ⟨m, -, -, rfl⟩ | ⟨op, -, -, rfl⟩ | ⟨m, -, hdgate, hnochain, hnoland, rfl⟩⟩ := hstep
    · cases m with
      | react rr =>
        rw [Network.applyHonest_react_sent] at hss
        rw [Network.applyHonest_react_received]
        by_cases hpp0 : p = p₀
        · rw [if_pos hpp0] at hss
          rcases List.mem_append.mp hss with hnew | hold
          · obtain ⟨st, hst, hseq⟩ := List.mem_map.mp hnew
            subst hseq
            rw [List.mem_append]
            refine Or.inl (List.mem_map.mpr ⟨st, ?_, rfl⟩)
            rw [List.mem_filter]
            refine ⟨hst, ?_⟩
            rw [hpp0] at hq
            simpa using hq
          · rw [List.mem_append]
            exact Or.inr (hP p ss hold q hq)
        · rw [if_neg hpp0] at hss
          rw [List.mem_append]
          exact Or.inr (hP p ss hss q hq)
      | wait dt =>
        have hrecv : (Network.applyHonest n p₀ (.wait dt)).received q = n.received q := by
          simp [Network.applyHonest]
        have hsent : (Network.applyHonest n p₀ (.wait dt)).sent = n.sent := by
          simp [Network.applyHonest]
        rw [hsent] at hss
        rw [hrecv]
        exact hP p ss hss q hq
    · cases hop : n.chain.apply apps p₀ op with
      | none =>
        have hsent : (Network.land apps n p₀ op).sent = n.sent := by simp [Network.land, hop]
        have hrecv : (Network.land apps n p₀ op).received q = n.received q := by
          simp [Network.land, hop]
        rw [hsent] at hss
        rw [hrecv]
        exact hP p ss hss q hq
      | some s' =>
        have hsent : (Network.land apps n p₀ op).sent = n.sent := by simp [Network.land, hop]
        have hrecv : (Network.land apps n p₀ op).received q = op.proofStates ++ n.received q := by
          simp [Network.land, hop]
        rw [hsent] at hss
        rw [hrecv]
        exact List.mem_append_right _ (hP p ss hss q hq)
    · cases m with
      | chain caller op => exact absurd rfl (hnochain caller op)
      | deliver ss' =>
        have hsent : (Network.applyAdv apps n p₀ (.deliver ss')).sent = n.sent := by
          simp [Network.applyAdv]
        have hrecv : (Network.applyAdv apps n p₀ (.deliver ss')).received q =
            if q = p₀ then ss' :: n.received q else n.received q := by
          simp [Network.applyAdv]
        rw [hsent] at hss
        rw [hrecv]
        by_cases hqp0 : q = p₀
        · rw [if_pos hqp0]; exact List.mem_cons_of_mem _ (hP p ss hss q hq)
        · rw [if_neg hqp0]; exact hP p ss hss q hq
      | tick dt =>
        have hsent : (Network.applyAdv apps n p₀ (.tick dt)).sent = n.sent := by
          simp [Network.applyAdv]
        have hrecv : (Network.applyAdv apps n p₀ (.tick dt)).received q = n.received q := by
          simp [Network.applyAdv]
        rw [hsent] at hss
        rw [hrecv]
        exact hP p ss hss q hq
      | land op => exact absurd rfl (hnoland op)

/-- **Every reachable `Network`'s views are `Views.Consistent`**, all
    three conjuncts, no further hypothesis. The first holds
    unconditionally (`Network.views_chain_eq`); the second is the
    synchronous-delivery fact (`Nitro.network_views_delivered`); the
    third is `Nitro.network_views_signers`. Every multi-view Liveness
    theorem that took `hv : v.Consistent` alongside `hr` derives it from
    `hr` alone. -/
theorem Nitro.network_views_consistent {apps : Apps E} {Ts : Threats E apps} {n : Network E}
    (h : (Nitro.network apps Ts).Reachable n) : n.views.Consistent :=
  ⟨Network.views_chain_eq n, Nitro.network_views_delivered h, Nitro.network_views_signers h⟩

/-- `base`'s view after receiving every `p₀`-sent state in `sends` that
    names it a recipient, batched as one list (helper for
    `Nitro.participant_reachable_deliver_sends`; a plain `def`, not an
    inline structure update, so it is one unambiguous term throughout). -/
def ArmadaLean.Nitro.NetworkState.recvBatch {q : Participant} (base : NetworkState E q) (p₀ : Participant)
    (sends : List (State E)) : NetworkState E q :=
  let batch : List (State E) := sends.filter (fun st => decide (q ∈ st.recipients p₀))
  { base with received := batch.map (fun st => (⟨st, [p₀]⟩ : SignedState E)) ++ base.received }

/-- **A bystander `q` of a multi-send reaction reaches every send meant for
    it, one `.deliver` at a time.** `Network.applyHonest`'s `.react` case
    delivers every recipient's whole batch in one `Network` step; from a
    single participant's own `Nitro.participant` machine, that batch is a
    `Relation.ReflTransGen` of one `.deliver` per relevant send instead —
    `Capable.capableDeliver` grants each one (`Unforged`: the only signer,
    `p₀ ≠ q`, so `q`'s own forgery check is vacuous; `VoucherSendable`
    covers the voucher, `hvgate`). Used by
    `Nitro.network_views_participant_reachable`'s `.react` case for `q ≠
    p₀`, generalizing the old single-`.send` case (`sends = [st]`). -/
theorem Nitro.participant_reachable_deliver_sends {apps : Apps E} {Ts : Threats E apps}
    {p₀ q : Participant} (hqp0 : q ≠ p₀) (sends : List (State E))
    {base : NetworkState E q} (hvg : ∀ st ∈ sends, ∀ v, st.voucher? = some v → q ∈ v.signers →
        ∃ s ∈ base.sent, s.state.voucher? = some v)
    (hbase : (Nitro.participant apps (Ts.T q)).Reachable base) :
    (Nitro.participant apps (Ts.T q)).Reachable (base.recvBatch p₀ sends) := by
  induction sends with
  | nil => simpa [NetworkState.recvBatch] using hbase
  | cons st rest ih =>
    have ihrest : (Nitro.participant apps (Ts.T q)).Reachable (base.recvBatch p₀ rest) :=
      ih (fun st' hst' => hvg st' (List.mem_cons_of_mem _ hst'))
    by_cases hqr : q ∈ st.recipients p₀
    · have hUnforged : NetworkState.Unforged (base.recvBatch p₀ rest) (⟨st, [p₀]⟩ : SignedState E) := by
        refine ⟨fun hqsg => ?_, fun v hv hqv => ?_⟩
        · simp only [List.mem_singleton] at hqsg
          exact absurd hqsg hqp0
        · exact hvg st List.mem_cons_self v hv hqv
      obtain ⟨s₀, hinit, hsteps⟩ := ihrest
      refine ⟨s₀, hinit, hsteps.tail (Or.inr (Or.inr
        ⟨.deliver ⟨st, [p₀]⟩, (Ts.ok q).toCapable.capableDeliver _ _ hUnforged, ?_⟩))⟩
      simp [NetworkState.recvBatch, NetworkState.applyAdv, hqr]
    · simpa [NetworkState.recvBatch, List.filter_cons, hqr] using ihrest

/-- **Every view of a reachable `Network` is `Nitro.participant`-reachable.**
    The caller rule (operator ruling 2026-10-29, "Caller rule", read
    literally: no adversary move is `.chain` or `.land`) removes the one
    gap the earlier channel-participant gloss left open. The mover `p₀`'s
    own view is always reachable as its own move (same witness, same
    feasibility, `Nitro.participant`'s step — a `.react` as `p₀`'s own
    honest branch, using `Network.applyHonest_react_sent`/`_received_self`
    to match `NetworkState.applyHonest`'s own `.react` arm exactly, or a
    landed call as `p₀`'s own `land` branch). Every OTHER participant
    `q`'s view changes three ways: `p₀`'s landed call broadcasts
    `op.proofStates` to `q`'s `received` — exactly `(n.view q).applyAdv
    apps (.chain p₀ op)`, and `Capable.capable` grants `(Ts.T q).feasible
    (n.view q) (.chain p₀ op)` from `p₀ ≠ q` (`Bounds.notHonest`'s own
    bound, read for `Ts.T p₀`, vacuously true here since the caller IS
    `p₀`) and `Network.Sendable` (`Unforged` for every signer, not only
    `q`'s); `p₀`'s send reaches `q`'s `received` exactly when `q` is a
    recipient — a `.deliver` of the one new entry; or the chain's clock
    ticks (`p₀`'s honest `.wait` or adversary `.tick`), shared, so it
    reaches `q` too — exactly `q`'s own adversary `.tick dt`, always
    feasible (`Capable.capableTick`). Every other case (`.react` to a
    non-recipient, `.deliver` to `p₀ ≠ q`) leaves `q`'s view untouched. No
    case needs `q` to be a channel participant; the caller rule rules out
    an adversary `.chain`/`.land` move outright, so there is no bystander
    case left to block. -/
theorem Nitro.network_views_participant_reachable {apps : Apps E} {Ts : Threats E apps}
    {n : Network E} (h : (Nitro.network apps Ts).Reachable n) (q : Participant) :
    (Nitro.participant apps (Ts.T q)).Reachable (n.view q) := by
  refine Machine.invariant (Nitro.network apps Ts)
    (P := fun n => (Nitro.participant apps (Ts.T q)).Reachable (n.view q)) ?_ ?_ n h
  · intro n hinit
    rw [hinit]
    exact ⟨_, rfl, Relation.ReflTransGen.refl⟩
  · intro n n' hP hstep
    obtain ⟨p₀, ⟨m, hfeas, hvgate, rfl⟩ | ⟨op, hfeas, hsgate, rfl⟩ | ⟨m, hfeas, -, hnochain, hnoland, rfl⟩⟩ :=
      hstep
    · by_cases hqp0 : q = p₀
      · subst hqp0
        have heq : (Network.applyHonest n q m).view q = (n.view q).applyHonest m := by
          cases m with
          | react rr =>
            simp [Network.view, Network.applyHonest_react_sent, Network.applyHonest_react_received_self,
              NetworkState.applyHonest]
          | wait dt => simp [Network.applyHonest, Network.view, NetworkState.applyHonest]
        rw [heq]
        exact hP.tail (Or.inl ⟨m, hfeas, rfl⟩)
      · cases m with
        | react rr =>
          have heq : (Network.applyHonest n p₀ (.react rr)).view q =
              (n.view q).recvBatch p₀ rr.sends := by
            simp [Network.view, Network.applyHonest_react_sent, hqp0,
              Network.applyHonest_react_received, NetworkState.recvBatch]
          rw [heq]
          refine Nitro.participant_reachable_deliver_sends hqp0 rr.sends ?_ hP
          intro st hst v hv hqv
          exact hvgate rr rfl st hst v hv q hqv
        | wait dt =>
          have heq : (Network.applyHonest n p₀ (.wait dt)).view q =
              (n.view q).applyAdv apps (.tick dt) := by
            simp [Network.applyHonest, Network.view, NetworkState.applyAdv]
          rw [heq]
          exact hP.tail (Or.inr (Or.inr ⟨.tick dt, (Ts.ok q).toCapable.capableTick _ dt, rfl⟩))
    · by_cases hqp0 : q = p₀
      · subst hqp0
        have heq : (Network.land apps n q op).view q = (n.view q).applyAdv apps (.land op) := by
          simp only [Network.land, Network.view, NetworkState.applyAdv]
          cases n.chain.apply apps q op <;> rfl
        rw [heq]
        exact hP.tail (Or.inr (Or.inl ⟨op, hfeas, rfl⟩))
      · have heq : (Network.land apps n p₀ op).view q =
            (n.view q).applyAdv apps (.chain p₀ op) := by
          simp only [Network.land, Network.view, NetworkState.applyAdv]
          cases n.chain.apply apps p₀ op <;> simp [if_neg hqp0]
        rw [heq]
        have hUnforged : ∀ ss ∈ op.proofStates, (n.view q).Unforged ss := by
          intro ss hss
          obtain ⟨hsg, hvoucher⟩ := hsgate ss hss
          exact ⟨fun hqsg => hsg q hqsg, fun v hv hqv => hvoucher v hv q hqv⟩
        have hcap : (Ts.T q).feasible (n.view q) (.chain p₀ op) :=
          (Ts.ok q).toCapable.capable (n.view q) p₀ op (Ne.symm hqp0) hUnforged
        exact hP.tail (Or.inr (Or.inr ⟨.chain p₀ op, hcap, rfl⟩))
    · by_cases hqp0 : q = p₀
      · subst hqp0
        have heq : (Network.applyAdv apps n q m).view q = (n.view q).applyAdv apps m := by
          cases m with
          | chain caller op => exact absurd rfl (hnochain caller op)
          | deliver ss => simp [Network.applyAdv, Network.view, NetworkState.applyAdv]
          | tick dt => simp [Network.applyAdv, Network.view, NetworkState.applyAdv]
          | land op => exact absurd rfl (hnoland op)
        rw [heq]
        exact hP.tail (Or.inr (Or.inr ⟨m, hfeas, rfl⟩))
      · cases m with
        | chain caller op => exact absurd rfl (hnochain caller op)
        | deliver ss =>
          have heq : (Network.applyAdv apps n p₀ (.deliver ss)).view q = n.view q := by
            simp [Network.applyAdv, Network.view, hqp0]
          rw [heq]
          exact hP
        | tick dt =>
          have heq : (Network.applyAdv apps n p₀ (.tick dt)).view q =
              (n.view q).applyAdv apps (.tick dt) := by
            simp [Network.applyAdv, Network.view, NetworkState.applyAdv]
          rw [heq]
          exact hP.tail (Or.inr (Or.inr ⟨.tick dt, (Ts.ok q).toCapable.capableTick _ dt, rfl⟩))
        | land op => exact absurd rfl (hnoland op)
