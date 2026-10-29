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
-/
import ArmadaLean.Machine
import ArmadaLean.Nitro.Strategy
import ArmadaLean.Nitro.Lemmas

namespace ArmadaLean.Nitro

variable {E : Type} [DecidableEq E]

/-- An honest move (`NetworkState.applyHonest`) never changes the chain
    except through a successful `Adjudicator.apply`, so it keeps `Reachable
    apps`: either the operation fails and the chain is unchanged
    (`Option.getD`), or it succeeds and is one `Step`. -/
theorem NetworkState.applyHonest_chain_reachable {apps : Apps E} {p : Participant}
    (net : NetworkState E p) (m : HonestMove E) (hr : Reachable apps net.chain) :
    Reachable apps (net.applyHonest apps m).chain := by
  cases m with
  | chain op =>
    simp only [NetworkState.applyHonest]
    cases h : net.chain.apply apps p op with
    | none => exact hr
    | some s' => exact hr.tail (Step.mk p op net.chain s' h)
  | send st => simpa [NetworkState.applyHonest] using hr
  | wait dt =>
    simp only [NetworkState.applyHonest]
    have happly : net.chain.apply apps p (.tick dt) = some (net.chain.tick dt) := rfl
    exact hr.tail (Step.mk p (.tick dt) net.chain (net.chain.tick dt) happly)

/-- An adversary move (`NetworkState.applyAdv`) never changes the chain
    except through a successful `Adjudicator.apply`, for the same reason as
    `NetworkState.applyHonest_chain_reachable`. `deliver` never touches the
    chain. -/
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
    moves (`NetworkState.applyHonest`, `HonestMove.Feasible`) or one
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
    (∃ m : HonestMove E, m.Feasible net ∧ net' = net.applyHonest apps m) ∨
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
    `NetworkState.applyAdv_chain_reachable` for the step case and
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
    rcases hstep with ⟨m, -, rfl⟩ | ⟨m, -, rfl⟩
    · exact NetworkState.applyHonest_chain_reachable net m hP
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

/-- `p`'s view of a `Network`: exactly `Strategy.lean:34`'s `NetworkState`,
    read off the shared chain and `p`'s own lists. -/
def Network.view (n : Network E) (p : Participant) : NetworkState E p :=
  ⟨n.chain, n.received p, n.sent p⟩

/-- The family of views `Views.Consistent` (`Strategy.lean:270`) and every
    multi-view Liveness theorem read. -/
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
    of an abstract `signed` list. Gates `Network.applyAdv`'s `.deliver`:
    see that definition's doc comment for why the per-participant model
    alone does not already enforce this. -/
def Network.Sendable (n : Network E) (ss : SignedState E) : Prop :=
  (∀ q ∈ ss.signers, ∃ s ∈ n.sent q, s.state = ss.state) ∧
  ∀ v, ss.state.voucher? = some v → ∀ q ∈ v.signers, ∃ s ∈ n.sent q, s.state.voucher? = some v

/-- One honest move of `p`, applied to the whole `Network`
    (`NetworkState.applyHonest`, `Strategy.lean:81`, read from `p`'s view).
    A successful `.chain` operation's proof states reach every OTHER
    participant's `received` (not `p`'s own, which `applyHonest`'s own
    `.chain` arm never touches, because `HonestMove.Feasible` already
    requires `p` to hold them before submitting): this generalizes the D9
    repair (`applyAdv`'s own `.chain` arm, `Strategy.lean:88-96`) from one
    adversary-modelled observer to the whole network, because an on-chain
    call is public, not visible to one observer only. -/
def Network.applyHonest (apps : Apps E) (n : Network E) (p : Participant) (m : HonestMove E) :
    Network E :=
  match m with
  | .chain op =>
    match n.chain.apply apps p op with
    | some s' =>
      { chain := s', sent := n.sent,
        received := fun q => if q = p then n.received q else op.proofStates ++ n.received q }
    | none => n
  | .send st => { n with sent := fun q => if q = p then ⟨st, [p]⟩ :: n.sent q else n.sent q }
  | .wait dt => { n with chain := n.chain.tick dt }

/-- One adversary move against `p`, applied to the whole `Network`
    (`NetworkState.applyAdv`, `Strategy.lean:97`, read from `p`'s view),
    with the same public-broadcast `.chain` case as `Network.applyHonest`.
    `.deliver ss` reaches only `p`'s own `received`: the per-participant
    model alone does not forbid delivering a forged OTHER signer's claim
    (`Bounds.unforgeable`/`NetworkState.Unforged` bound only `p`'s own
    alleged signature, by design, `Strategy.lean:129-135`), so
    `Nitro.network`'s step additionally requires `Network.Sendable ss`. -/
def Network.applyAdv (apps : Apps E) (n : Network E) (p : Participant) (m : AdvMove E) :
    Network E :=
  match m with
  | .chain caller op =>
    match n.chain.apply apps caller op with
    | some s' => { chain := s', sent := n.sent, received := fun q => op.proofStates ++ n.received q }
    | none => n
  | .deliver ss => { n with received := fun q => if q = p then ss :: n.received q else n.received q }
  | .tick dt => { n with chain := n.chain.tick dt }

theorem Network.applyHonest_chain_reachable {apps : Apps E} (n : Network E) (p : Participant)
    (m : HonestMove E) (hr : Reachable apps n.chain) :
    Reachable apps (Network.applyHonest apps n p m).chain := by
  cases m with
  | chain op =>
    simp only [Network.applyHonest]
    cases h : n.chain.apply apps p op with
    | none => exact hr
    | some s' => exact hr.tail (Step.mk p op n.chain s' h)
  | send st => simpa [Network.applyHonest] using hr
  | wait dt =>
    simp only [Network.applyHonest]
    have happly : n.chain.apply apps p (.tick dt) = some (n.chain.tick dt) := rfl
    exact hr.tail (Step.mk p (.tick dt) n.chain (n.chain.tick dt) happly)

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

/-- The network game: at each step, some participant `p` makes one of its
    own feasible honest moves, or `p`'s own adversary `Ts.T p` makes one
    feasible move against `p`, gated by `Network.Sendable` for a
    delivery. Operator ruling 2026-10-29: `ReachableViews`
    (`Nitro.network apps Ts).Reachable`, not a separate predicate. -/
def Nitro.network (apps : Apps E) (Ts : Threats E apps) : Machine (Network E) where
  init := fun n => n = ⟨Adjudicator.genesis, fun _ => [], fun _ => []⟩
  step := fun n n' => ∃ p : Participant,
    (∃ m : HonestMove E, m.Feasible (n.view p) ∧ n' = Network.applyHonest apps n p m) ∨
    (∃ m : AdvMove E, (Ts.T p).feasible (n.view p) m ∧
      (∀ ss, m = .deliver ss → n.Sendable ss) ∧
      n' = Network.applyAdv apps n p m)

/-- **The chain of a reachable `Network` is reachable.** By
    `Machine.invariant`, using `Network.applyHonest_chain_reachable` /
    `Network.applyAdv_chain_reachable` for the step case. -/
theorem Nitro.network_chain_reachable {apps : Apps E} {Ts : Threats E apps} {n : Network E}
    (h : (Nitro.network apps Ts).Reachable n) : Reachable apps n.chain := by
  refine Machine.invariant (Nitro.network apps Ts) (P := fun n => Reachable apps n.chain) ?_ ?_ n h
  · intro n hinit
    rw [hinit]
    exact Relation.ReflTransGen.refl
  · intro n n' hP hstep
    obtain ⟨p, ⟨m, -, rfl⟩ | ⟨m, -, -, rfl⟩⟩ := hstep
    · exact Network.applyHonest_chain_reachable n p m hP
    · exact Network.applyAdv_chain_reachable n p m hP

/- **Finding (not proved, and not provable with the structures this draft
    has): `(Nitro.network apps Ts).Reachable n` does not give
    `(Network.views n).Consistent`.** `Views.Consistent`'s first conjunct
    (`Network.views_chain_eq`) holds unconditionally. The other two do not:

    - Conjunct 2 (`∀ p q, p ≠ q → ∀ ss ∈ (v p).sent, ss ∈ (v q).received`,
      "p sent it, q has it"): false at the one-step reachable `n` built from
      genesis by a single honest `.send st` move of `p`. `Network.applyHonest`'s
      `.send` case touches only `n.sent`; no participant's `received`
      changes. So `st ∈ n'.sent p` and `st ∉ n'.received q` for every `q`.
      This is not a bug to fix: a sent, undelivered message is exactly the
      asynchrony (front-running) the whole game models (Nitro:537-539), and
      the coordinator's own design keeps delivery a separate adversary
      step, never bundled with send.
    - Conjunct 3 (`∀ p q, p ≠ q → ∀ r ∈ (v p).received, q ∈ r.signers →
      ∃ s ∈ (v q).sent, s.state = r.state`, "a claimed signer really
      signed"): holds for a `received` entry that arrived through
      `Network.applyAdv`'s `.deliver` case, by `Network.Sendable`'s own
      statement. It is not provable for an entry that arrived through the
      `.chain` broadcast case (`Network.applyHonest`/`Network.applyAdv`):
      that case is gated only by `HonestMove.Feasible`/`Bounds.unforgeable`,
      which (`Strategy.lean:129-135`, `NetworkState.Unforged`) bound only
      the acting view's OWN alleged signature, not every signer a proof
      state names. Closing this needs a network-wide custody invariant —
      every entry in every participant's `received`, traced back
      transitively, resolves to a real `sent` entry — which this draft
      does not state or prove.

    Both gaps trace to the same cause: the per-participant `Assumptions`
    (`Strategy.lean:162`) bound only the forgery risk to the one
    participant being modelled; a second, system-wide assumption
    (SATP:168, "forging a signature is infeasible", read for every
    participant at once) is what `Views.Consistent` has always stood in
    for, and `hv : v.Consistent` stays an independent hypothesis next to
    `hr : (Nitro.network apps Ts).Reachable n` in every multi-view theorem
    — reachability does not subsume it. The same cause is why this file
    does not state "every view of a reachable `Network` is
    `Nitro.participant`-reachable": the mover's own view always is (the
    same move `m` with the same feasibility witness the `Network` step
    already carries), but another participant `q`'s view, when it changes
    only through the `.chain` broadcast, needs `(Ts.T q).feasible (n.view
    q) (.chain p op)`, which `Capable.capable` (`Strategy.lean:153`) grants
    only given `∀ ss ∈ op.proofStates, (n.view q).Unforged ss` — the same
    missing custody invariant. -/
