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
    feasible move against `p`. `Network.Sendable` gates a `.deliver` and
    every `.chain` operation's proof states: SATP:168 "forging
    cryptographic signatures is infeasible" is a system-wide fact,
    already encoded on the chain side by `ReachableSigned`'s own
    hypothesis (`Adjudicator.lean:331`, `SignedStep`'s `hsig`); this is
    the same fact for the network's own `sent` record, so every
    signature a proof state carries is genuine, not only the acting
    view's own. The caller rule (operator ruling 2026-10-29, "Caller
    rule",
    `armada-laconic/labbook/2026-10-29-machine-types-for-approval.md`
    §"Result" item 3, read literally): "only q's own honest moves may
    submit an on-chain call with caller q" — for every participant, not
    only a channel's. An adversary move is never a `.chain` move at
    all: every on-chain call is `p`'s own `Op.proofStates`-held, honest
    `.chain op` (Nitro:312-313 "anyone can trigger an operation" reads,
    for this model, as "the caller is that participant, using its own
    `Feasible` move"), so the adversary's moves are only `.deliver` and
    `.tick`. Operator ruling 2026-10-29: `ReachableViews` is
    `(Nitro.network apps Ts).Reachable`, not a separate predicate. -/
def Nitro.network (apps : Apps E) (Ts : Threats E apps) : Machine (Network E) where
  init := fun n => n = ⟨Adjudicator.genesis, fun _ => [], fun _ => []⟩
  step := fun n n' => ∃ p : Participant,
    (∃ m : HonestMove E, m.Feasible (n.view p) ∧
      (∀ op, m = .chain op → ∀ ss ∈ op.proofStates, n.Sendable ss) ∧
      n' = Network.applyHonest apps n p m) ∨
    (∃ m : AdvMove E, (Ts.T p).feasible (n.view p) m ∧
      (∀ ss, m = .deliver ss → n.Sendable ss) ∧
      (∀ caller op, m ≠ .chain caller op) ∧
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
    obtain ⟨p, ⟨m, -, -, rfl⟩ | ⟨m, -, -, -, rfl⟩⟩ := hstep
    · exact Network.applyHonest_chain_reachable n p m hP
    · exact Network.applyAdv_chain_reachable n p m hP

/-- **`Views.Consistent`'s third conjunct holds for every reachable
    `Network`.** A state `p` received that names `q` as a signer is a
    state `q` really sent. By `Machine.invariant`: at genesis every
    `received` is empty (vacuous); a step leaves `received` untouched
    (`.send`, `.wait`, `.tick`), touches only the mover's own `received`
    through a `Network.Sendable`-gated `.deliver` (whose statement is
    exactly this conjunct for the one new entry), or broadcasts a
    `.chain` operation's `Network.Sendable`-gated proof states (same
    argument, for every new entry at once). -/
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
    obtain ⟨p₀, ⟨m, -, hgate, rfl⟩ | ⟨m, -, hdgate, hnochain, rfl⟩⟩ := hstep
    · cases m with
      | chain op =>
        cases hop : n.chain.apply apps p₀ op with
        | none =>
          have hsent : (Network.applyHonest apps n p₀ (.chain op)).sent = n.sent := by
            simp [Network.applyHonest, hop]
          have hrecv : (Network.applyHonest apps n p₀ (.chain op)).received p = n.received p := by
            simp [Network.applyHonest, hop]
          rw [hsent]
          rw [hrecv] at hr
          exact hP p q hpq r hr hqr
        | some s' =>
          have hsent : (Network.applyHonest apps n p₀ (.chain op)).sent = n.sent := by
            simp [Network.applyHonest, hop]
          have hrecv : (Network.applyHonest apps n p₀ (.chain op)).received p =
              if p = p₀ then n.received p else op.proofStates ++ n.received p := by
            simp [Network.applyHonest, hop]
          rw [hsent]
          rw [hrecv] at hr
          by_cases hpp0 : p = p₀
          · rw [if_pos hpp0] at hr
            exact hP p q hpq r hr hqr
          · rw [if_neg hpp0] at hr
            rcases List.mem_append.mp hr with hnew | hold
            · exact (hgate op rfl r hnew).1 q hqr
            · exact hP p q hpq r hold hqr
      | send st =>
        have hrecv : (Network.applyHonest apps n p₀ (.send st)).received p = n.received p := by
          simp [Network.applyHonest]
        have hsent : (Network.applyHonest apps n p₀ (.send st)).sent q =
            if q = p₀ then ⟨st, [p₀]⟩ :: n.sent q else n.sent q := by
          simp [Network.applyHonest]
        rw [hrecv] at hr
        obtain ⟨s, hs, hseq⟩ := hP p q hpq r hr hqr
        refine ⟨s, ?_, hseq⟩
        rw [hsent]
        by_cases hqp0 : q = p₀
        · rw [if_pos hqp0]; exact List.mem_cons_of_mem _ hs
        · rw [if_neg hqp0]; exact hs
      | wait dt =>
        have hrecv : (Network.applyHonest apps n p₀ (.wait dt)).received p = n.received p := by
          simp [Network.applyHonest]
        have hsent : (Network.applyHonest apps n p₀ (.wait dt)).sent = n.sent := by
          simp [Network.applyHonest]
        rw [hrecv] at hr
        rw [hsent]
        exact hP p q hpq r hr hqr
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
    (`Address.lean:36`, a bare `Nat` wrapper) is infinite, so no single
    flat list can be "all of `n.sent`" at once; the existential below is
    the finite record one actual reachability derivation builds, carried
    along the same induction as `Nitro.network_views_signers`:
    `Network.Sendable`, gated on every `.chain` operation's proof states
    by `Nitro.network`'s step, is `SignedState.SignedIn` read against
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
    obtain ⟨p₀, ⟨m, -, hgate, rfl⟩ | ⟨m, -, -, hnochain, rfl⟩⟩ := hstep
    · cases m with
      | chain op =>
        cases hop : n.chain.apply apps p₀ op with
        | none =>
          refine ⟨signed, ?_, ?_⟩
          · have hc : (Network.applyHonest apps n p₀ (.chain op)).chain = n.chain := by
              simp [Network.applyHonest, hop]
            rw [hc]; exact hreach
          · have hs : (Network.applyHonest apps n p₀ (.chain op)).sent = n.sent := by
              simp [Network.applyHonest, hop]
            rw [hs]; exact hmirror
        | some s' =>
          have hc : (Network.applyHonest apps n p₀ (.chain op)).chain = s' := by
            simp [Network.applyHonest, hop]
          have hs : (Network.applyHonest apps n p₀ (.chain op)).sent = n.sent := by
            simp [Network.applyHonest, hop]
          refine ⟨signed, ?_, by rw [hs]; exact hmirror⟩
          rw [hc]
          refine hreach.tail ⟨p₀, op, _, _, ?_, hop⟩
          intro ss hss
          obtain ⟨hsg, hvoucher⟩ := hgate op rfl ss hss
          refine ⟨fun q' hq' => ?_, fun v hv q' hq' => ?_⟩
          · obtain ⟨s, hs', hseq⟩ := hsg q' hq'
            exact (hmirror q' ss.state).mpr ⟨s, hs', hseq⟩
          · obtain ⟨s, hs', hseq⟩ := hvoucher v hv q' hq'
            exact ⟨s.state, (hmirror q' s.state).mpr ⟨s, hs', rfl⟩, hseq⟩
      | send st =>
        have hc : (Network.applyHonest apps n p₀ (.send st)).chain = n.chain := by
          simp [Network.applyHonest]
        refine ⟨(p₀, st) :: signed, ?_, ?_⟩
        · rw [hc]; exact ReachableSigned.mono (fun x hx => List.mem_cons_of_mem _ hx) hreach
        · intro q st'
          have hs : (Network.applyHonest apps n p₀ (.send st)).sent q =
              if q = p₀ then ⟨st, [p₀]⟩ :: n.sent q else n.sent q := by
            simp [Network.applyHonest]
          rw [hs]
          by_cases hqp0 : q = p₀
          · subst hqp0
            rw [if_pos rfl]
            simp only [List.mem_cons]
            constructor
            · rintro (heq | hmem)
              · injection heq with h1 h2
                exact ⟨⟨st, [q]⟩, Or.inl rfl, h2.symm⟩
              · obtain ⟨s, hs', hseq⟩ := (hmirror q st').mp hmem
                exact ⟨s, Or.inr hs', hseq⟩
            · rintro ⟨s, (hs' | hs'), hseq⟩
              · subst hs'
                subst hseq
                exact Or.inl rfl
              · exact Or.inr ((hmirror q st').mpr ⟨s, hs', hseq⟩)
          · rw [if_neg hqp0, List.mem_cons]
            constructor
            · rintro (heq | hmem)
              · injection heq with h1 h2
                exact absurd h1 hqp0
              · exact (hmirror q st').mp hmem
            · intro hmem
              exact Or.inr ((hmirror q st').mpr hmem)
      | wait dt =>
        have hc : (Network.applyHonest apps n p₀ (.wait dt)).chain = n.chain.tick dt := by
          simp [Network.applyHonest]
        have hs : (Network.applyHonest apps n p₀ (.wait dt)).sent = n.sent := by
          simp [Network.applyHonest]
        refine ⟨signed, ?_, by rw [hs]; exact hmirror⟩
        rw [hc]
        refine hreach.tail ⟨p₀, .tick dt, _, _, ?_, rfl⟩
        simp [Op.proofStates]
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

/-- **For a reachable `Network`, `Views.Consistent` means exactly that
    every sent state has been delivered.** `Views.Consistent`'s first
    conjunct holds unconditionally (`Network.views_chain_eq`), and its
    third holds for every reachable `Network` (`Nitro.network_views_signers`).
    What `hv : v.Consistent` adds, once `v = n.views` and `n` is
    reachable, is exactly the delivery conjunct — the one synchrony
    assumption the game does not get for free (Nitro:537-539). -/
theorem Nitro.network_views_consistent_iff {apps : Apps E} {Ts : Threats E apps} {n : Network E}
    (h : (Nitro.network apps Ts).Reachable n) :
    n.views.Consistent ↔
      ∀ p q : Participant, p ≠ q → ∀ ss ∈ (n.views p).sent, ss ∈ (n.views q).received :=
  ⟨fun hc => hc.2.1, fun hdeliv => ⟨Network.views_chain_eq n, hdeliv, Nitro.network_views_signers h⟩⟩

/-- **Every view of a reachable `Network` is `Nitro.participant`-reachable.**
    The caller rule (operator ruling 2026-10-29, "Caller rule", read
    literally: no adversary move is `.chain`) removes the one gap the
    earlier channel-participant gloss left open. The mover `p₀`'s own
    view is always reachable as its own move (same witness, same
    feasibility, `Nitro.participant`'s step). Every OTHER participant
    `q`'s view changes only two ways: `p₀`'s honest `.chain op` broadcasts
    `op.proofStates` to `q`'s `received` — exactly `(n.view q).applyAdv
    apps (.chain p₀ op)`, and `Capable.capable` (`Strategy.lean:153`)
    grants `(Ts.T q).feasible (n.view q) (.chain p₀ op)` from `p₀ ≠ q`
    (`Bounds.notHonest`'s own bound, read for `Ts.T p₀`, vacuously true
    here since the caller IS `p₀`) and `Network.Sendable` (`Unforged` for
    every signer, not only `q`'s); or the chain's clock ticks (`p₀`'s
    honest `.wait` or adversary `.tick`), shared, so it reaches `q` too —
    exactly `q`'s own adversary `.tick dt`, always feasible
    (`Capable.capableTick`). Every other case (`.send`, `.deliver` to
    `p₀ ≠ q`) leaves `q`'s view untouched. No case needs `q` to be a
    channel participant; the caller rule rules out an adversary `.chain`
    move outright, so there is no bystander case left to block. -/
theorem Nitro.network_views_participant_reachable {apps : Apps E} {Ts : Threats E apps}
    {n : Network E} (h : (Nitro.network apps Ts).Reachable n) (q : Participant) :
    (Nitro.participant apps (Ts.T q)).Reachable (n.view q) := by
  refine Machine.invariant (Nitro.network apps Ts)
    (P := fun n => (Nitro.participant apps (Ts.T q)).Reachable (n.view q)) ?_ ?_ n h
  · intro n hinit
    rw [hinit]
    exact ⟨_, rfl, Relation.ReflTransGen.refl⟩
  · intro n n' hP hstep
    obtain ⟨p₀, ⟨m, hfeas, hgate, rfl⟩ | ⟨m, hfeas, -, hnochain, rfl⟩⟩ := hstep
    · by_cases hqp0 : q = p₀
      · subst hqp0
        have heq : (Network.applyHonest apps n q m).view q = (n.view q).applyHonest apps m := by
          cases m with
          | chain op =>
            cases hop : n.chain.apply apps q op with
            | none => simp [Network.applyHonest, hop, Network.view, NetworkState.applyHonest]
            | some s' =>
              simp [Network.applyHonest, hop, Network.view, NetworkState.applyHonest]
          | send st => simp [Network.applyHonest, Network.view, NetworkState.applyHonest]
          | wait dt => simp [Network.applyHonest, Network.view, NetworkState.applyHonest]
        rw [heq]
        exact hP.tail (Or.inl ⟨m, hfeas, rfl⟩)
      · cases m with
        | chain op =>
          have heq : (Network.applyHonest apps n p₀ (.chain op)).view q =
              (n.view q).applyAdv apps (.chain p₀ op) := by
            cases hop : n.chain.apply apps p₀ op with
            | none => simp [Network.applyHonest, hop, Network.view, NetworkState.applyAdv]
            | some s' =>
              simp [Network.applyHonest, hop, Network.view, NetworkState.applyAdv, if_neg hqp0]
          rw [heq]
          have hUnforged : ∀ ss ∈ op.proofStates, (n.view q).Unforged ss := by
            intro ss hss
            obtain ⟨hsg, hvoucher⟩ := hgate op rfl ss hss
            exact ⟨fun hqsg => hsg q hqsg, fun v hv hqv => hvoucher v hv q hqv⟩
          have hcap : (Ts.T q).feasible (n.view q) (.chain p₀ op) :=
            (Ts.ok q).toCapable.capable (n.view q) p₀ op (Ne.symm hqp0) hUnforged
          exact hP.tail (Or.inr ⟨.chain p₀ op, hcap, rfl⟩)
        | send st =>
          have heq : (Network.applyHonest apps n p₀ (.send st)).view q = n.view q := by
            simp [Network.applyHonest, Network.view, hqp0]
          rw [heq]
          exact hP
        | wait dt =>
          have heq : (Network.applyHonest apps n p₀ (.wait dt)).view q =
              (n.view q).applyAdv apps (.tick dt) := by
            simp [Network.applyHonest, Network.view, NetworkState.applyAdv]
          rw [heq]
          exact hP.tail (Or.inr ⟨.tick dt, (Ts.ok q).toCapable.capableTick _ dt, rfl⟩)
    · by_cases hqp0 : q = p₀
      · subst hqp0
        have heq : (Network.applyAdv apps n q m).view q = (n.view q).applyAdv apps m := by
          cases m with
          | chain caller op => exact absurd rfl (hnochain caller op)
          | deliver ss => simp [Network.applyAdv, Network.view, NetworkState.applyAdv]
          | tick dt => simp [Network.applyAdv, Network.view, NetworkState.applyAdv]
        rw [heq]
        exact hP.tail (Or.inr ⟨m, hfeas, rfl⟩)
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
          exact hP.tail (Or.inr ⟨.tick dt, (Ts.ok q).toCapable.capableTick _ dt, rfl⟩)
