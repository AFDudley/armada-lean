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

/-- The joint network game: `p : Participant ↦ NetworkState E p` composed by
    `Machine.interleave`, one `Nitro.participant` machine per participant.
    Each participant's own moves (honest and that participant's adversary)
    are independent of every other participant's, except as
    `Views.Consistent` (`Strategy.lean:270`) separately states; this is
    exactly `Machine.interleave`'s no-shared-state shape. A single
    composition over `Participant` covers both the single-view and
    multi-view Liveness theorems: `(Nitro.network apps Ts).Reachable`
    reads `Views E := ∀ p, NetworkState E p` directly (operator ruling
    2026-10-29); a single-view theorem's `net : NetworkState E p` instead
    takes `(Nitro.participant apps T).Reachable net`, because a single-view
    theorem carries only its own `T : Threat E p`, not a whole `Threats E
    apps` family — threading one through only to immediately project back
    out with `Machine.interleave_reachable_component` would add an unused
    parameter to every other participant's assumptions for no gain. This
    is the shape choice the operator ruling leaves open; flag for approval
    alongside the definition. -/
def Nitro.network (apps : Apps E) (Ts : Threats E apps) : Machine (Views E) :=
  Machine.interleave (fun p => Nitro.participant apps (Ts.T p))

/-- A reachable `Nitro.network` state's view at `p` is itself
    `Nitro.participant`-reachable against `p`'s own threat
    (`Machine.interleave_reachable_component`). -/
theorem Nitro.network_reachable_component {apps : Apps E} {Ts : Threats E apps} {v : Views E}
    (h : (Nitro.network apps Ts).Reachable v) (p : Participant) :
    (Nitro.participant apps (Ts.T p)).Reachable (v p) :=
  Machine.interleave_reachable_component _ h p

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

/-- The chain of a `Nitro.network`-reachable view at `p` is reachable:
    project to `p`'s own `Nitro.participant` machine
    (`Nitro.network_reachable_component`), then
    `Nitro.participant_chain_reachable`. -/
theorem Nitro.network_chain_reachable {apps : Apps E} {Ts : Threats E apps} {v : Views E}
    (h : (Nitro.network apps Ts).Reachable v) (p : Participant) :
    Reachable apps (v p).chain :=
  Nitro.participant_chain_reachable (Nitro.network_reachable_component h p)
