/-
  Nitro protocol specification: reachable network states. The
  Liveness theorems assume a reachable network state, "views reachable from
  a genesis network (the genesis chain, empty sent and received lists) by
  honest moves and adversary rounds". The 2026-10-29 "Generic state:
  `Machine` and `System`" addendum: network reachability is the composed
  machine's `Machine.Reachable`, not a separate predicate. This file states
  the network game as a `Machine` and connects it to `Adjudicator.lean`'s
  existing chain-only `Reachable`.

  Explicit-time game ("Time bounds per pending
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
import ArmadaLean.Types.Reachable
import ArmadaLean.Nitro.Strategy
import ArmadaLean.Nitro.Invariant
import ArmadaLean.Nitro.Lemmas
import ArmadaLean.SpecTools
import Mathlib.Tactic.Says

namespace ArmadaLean

section

open ArmadaLean.Nitro

variable {E : Type} [DecidableEq E]

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

/-- `Nitro.signedChain apps signed`: the chain alone as a `Machine` whose steps
    use only the signatures in `signed` (`SignedStep`, `Adjudicator.lean:323`),
    from `Adjudicator.genesis`. Its reachable states are `ReachableSigned apps
    signed` (`Adjudicator.lean:331`; SATP:168: forging a signature is
    infeasible), so a statement over them takes the type
    `ReachableState (Nitro.signedChain apps signed)` (operator decision
    2026-10-31: reachability is a type). -/
def Nitro.signedChain (apps : Apps E) (signed : List (Participant × State E)) :
    Machine (Adjudicator E) where
  init := fun s => s = Adjudicator.genesis
  step := SignedStep apps signed

/-- `Nitro.signedChain apps signed`'s `Machine.Reachable` is exactly
    `ReachableSigned apps signed` (`Adjudicator.lean:331`): both are the empty
    state closed under `SignedStep apps signed` by `Relation.ReflTransGen`. -/
theorem Nitro.signedChain_reachable_iff {apps : Apps E} {signed : List (Participant × State E)}
    {s : Adjudicator E} :
    (Nitro.signedChain apps signed).Reachable s ↔ ReachableSigned apps signed s := by
  constructor
  · rintro ⟨s₀, rfl, hsteps⟩
    exact hsteps
  · intro hr
    exact ⟨Adjudicator.genesis, rfl, hr⟩

end

end ArmadaLean

namespace ArmadaLean.Nitro

variable {E : Type} [DecidableEq E]

/-- An honest move (`NetworkState.applyHonest`) never touches the chain: a
    reaction's sends only ever touch `sent`, and its calls land separately
    (`.land`, below), not here. -/
theorem NetworkState.applyHonest_chain_reachable {apps : Apps E} {p : Participant}
    (net : NetworkState E p) (m : HonestMove E) (hr : Reachable apps net.chain) :
    Reachable apps (net.applyHonest m).chain := by
  cases m with
  | react r => (simpa? [NetworkState.applyHonest] using hr says simpa only [applyHonest] using hr)
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
    cases h : net.chain.apply apps caller op with
    | none =>
      simp only [NetworkState.applyAdv_chain_none apps h]
      exact hr
    | some s' =>
      simp only [NetworkState.applyAdv_chain_some apps h]
      exact hr.tail (Step.mk caller op net.chain s' h)
  | deliver ss => (simpa? using hr says simpa only [applyAdv_deliver] using hr)
  | tick dt =>
    simp only [NetworkState.applyAdv_tick apps]
    have happly : net.chain.apply apps p (.tick dt) = some (net.chain.tick dt) := rfl
    exact hr.tail (Step.mk p (.tick dt) net.chain (net.chain.tick dt) happly)
  | land op =>
    cases h : net.chain.apply apps p op with
    | none =>
      simp only [NetworkState.applyAdv_land_none apps h]
      exact hr
    | some s' =>
      simp only [NetworkState.applyAdv_land_some apps h]
      exact hr.tail (Step.mk p op net.chain s' h)

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
      (simp? [Address.fundable, hk] at hbf says simp only [Address.fundable, hk, reduceCtorEq, decide_false, Bool.false_eq_true] at hbf)
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
    (simpa? using ih says simpa only [FixedPart.address_eq, Adjudicator.setStatus_balances] using ih)
  | challenge c' proof candidate =>
    obtain ⟨_, rfl⟩ := Adjudicator.challenge_some h
    (simpa? using ih says simpa only [Adjudicator.setStatus_balances] using ih)
  | checkpoint c' proof candidate =>
    obtain ⟨_, rfl⟩ := Adjudicator.checkpoint_some h
    (simpa? using ih says simpa only [Adjudicator.setStatus_balances] using ih)
  | conclude c' ss =>
    obtain ⟨_, rfl⟩ := Adjudicator.conclude_some h
    (simpa? using ih says simpa only [Adjudicator.setStatus_balances] using ih)
  | tick dt =>
    (simp? at h says simp only [Adjudicator.apply_tick, Option.some.injEq] at h)
    subst h
    (simpa? using ih says simpa only [Adjudicator.tick_balances] using ih)

/-- **A reachable chain holds no coins in a virtual-kind channel.** Design
    decision 2026-10-29: the counterexamples to `directly_funded_pays`,
    `finalizable_funded_pays` and `ledger_partial_withdrawal` each put coins
    in a virtual-kind channel, which `deposit` and `transfer` refuse
    (`Adjudicator.deposit`, `Adjudicator.transfer`,
    `Adjudicator.lean:100-152`). Genesis holds no balances at all
    (`Adjudicator.genesis`, `Balances.get` on `[]`); every step keeps a
    virtual channel's balance at zero (`balances_virtual_zero_step`). -/
theorem Reachable.balances_virtual_zero {apps : Apps E} (s : ReachableState (Nitro.chain apps))
    (c : FixedPart) (hk : c.kind = .virtual) :
    s.state.balances.get (.channel c) = 0 := by
  obtain_reach ⟨s, hr : Reachable apps s⟩ := s
  induction hr with
  | refl => rfl
  | tail _ hstep ih =>
    obtain ⟨caller, op, _, _, happ⟩ := hstep
    exact balances_virtual_zero_step hk ih happ

end ArmadaLean.Nitro

namespace ArmadaLean

open ArmadaLean.Nitro

variable {E : Type} [DecidableEq E]

/-- `p`'s own machine, with its honest step gated by `honest`: from the
    empty state (`Adjudicator.genesis`, empty
    `sent` and `received`, Nitro:446-454), one of `p`'s own honest moves
    that `honest` allows (`NetworkState.applyHonest`; `Nitro.participant`
    gates it by `HonestMove.Feasible`), `p` landing
    one of its own currently-feasible calls directly (`land`, the
    explicit-time game's two-phase issue/land split collapsed back to one
    step, sound for bare reachability — this file's header), one
    feasible NON-LANDING move of the adversary `T` (`NetworkState.applyAdv`,
    `Threat.feasible`, gated `∀ op, m ≠ .land op`:
    signatures cannot be forged anywhere in armada-lean, so the
    `Threat.RoundSeq.other`'s own `hnoland` field exactly, and
    `Strategy.lean:215-218`'s doc comment, which already says `feasible` "is
    never consulted for `.land`" — landings come only from the honest-
    landing disjunct below and the deposit disjunct, so the unforgeability
    assumption (`Bounds.unforgeable`/`unforgeableDeliver`) holds on every
    path that grows `received`), or `p` landing a deposit (D10 design decision,
    `Network.deposit`'s own doc comment): `NetworkState` carries no
    wallet, so `p`'s own machine admits ANY amount, a sound
    over-approximation of the wallet-bounded `Nitro.network` step (this
    file's header: bare reachability over-approximates) — exactly what
    `Nitro.network_views_participant_reachable` needs at `q = p₀`.
    Declared as `Nitro.…` inside `namespace ArmadaLean`, not inside
    `namespace ArmadaLean.Nitro` (which already holds `NetworkState`,
    `Threat`, ...), so its full name is `ArmadaLean.Nitro.participant`, not
    `ArmadaLean.Nitro.Nitro.participant`; this mirrors
    `ArmadaLean.Pool.machine` (`PoolMachine.lean`). -/
def Nitro.participantWith (apps : Apps E) {p : Participant} (T : Threat E p)
    (honest : NetworkState E p → HonestMove E → Prop) : Machine (NetworkState E p) where
  init := fun net => net = ⟨Adjudicator.genesis, [], []⟩
  step := fun net net' =>
    (∃ m : HonestMove E, honest net m ∧ net' = net.applyHonest m) ∨
    (∃ op : Op E, op.HonestFeasible net ∧ net' = net.applyAdv apps (.land op)) ∨
    (∃ m : AdvMove E, T.feasible net m ∧ (∀ op, m ≠ .land op) ∧ net' = net.applyAdv apps m) ∨
    (∃ a : Address E, ∃ e x : Coins, net' = net.applyAdv apps (.land (.deposit a e x)))

/-- `p`'s own machine (`Nitro.participantWith`): an honest move must be
    feasible (`HonestMove.Feasible`), so every send satisfies the signing
    rules of `HonestSend` (`Types/Honest.lean`,
    option A). `Nitro.participant_sent_honest` is the invariant. -/
def Nitro.participant (apps : Apps E) {p : Participant} (T : Threat E p) :
    Machine (NetworkState E p) :=
  Nitro.participantWith apps T (fun net m => m.Feasible apps net)

/-- `p`'s own machine with no signing rule: an honest move needs only
    feasible calls (`HonestMove.CallsFeasible`), so `p` may sign against
    `HonestSend`. Only counterexamples that need such a `p` use it
    (`docs/counterexamples/`, each with its own reachability steps); no
    declaration of the library is stated over it. -/
def Nitro.participantUnrestricted (apps : Apps E) {p : Participant} (T : Threat E p) :
    Machine (NetworkState E p) :=
  Nitro.participantWith apps T (fun net m => m.CallsFeasible net)

/-- The reachable states of `p`'s own machine (`Nitro.participant`), as a type
    (`ArmadaLean/Types/Reachable.lean`; operator decision 2026-10-31). -/
abbrev Nitro.ReachableParticipant (apps : Apps E) {p : Participant} (T : Threat E p) : Type :=
  ReachableState (Nitro.participant apps T)

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
    rcases hstep with ⟨m, -, rfl⟩ | ⟨op, -, rfl⟩ | ⟨m, -, -, rfl⟩ | ⟨a, e, x, rfl⟩
    · exact NetworkState.applyHonest_chain_reachable net m hP
    · exact NetworkState.applyAdv_chain_reachable net (.land op) hP
    · exact NetworkState.applyAdv_chain_reachable net m hP
    · exact NetworkState.applyAdv_chain_reachable net (.land (.deposit a e x)) hP


/-- **Every received state of a reachable `Nitro.participant` is unforged**
    (design decision 2026-10-31: no signature can be forged anywhere in
    this model). By `Machine.invariant`: the initial state's `received` is
    empty, vacuously true; each step either leaves `received` untouched
    (an honest `.react`/`.wait`, or an adversary `.tick`/`.chain`/`.deliver`
    that targets no new state beyond what `Bounds` already bounds), or
    prepends `op.proofStates` for a landing (`p`'s own, honest-feasible —
    `Op.HonestFeasible.mem` plus `NetworkState.Holds.unforged` close the
    loop against the inductive hypothesis — or the adversary's own
    `.chain caller op`, bound directly by `Bounds.unforgeable`), or a
    single `.deliver ss`, bound by `Bounds.unforgeableDeliver`. The repaired
    step relation (`Nitro.participant`'s own doc comment) rules out the
    adversary ever landing a call itself, so this is now sound on every
    path that grows `received`. -/
theorem Nitro.participant_received_unforged {apps : Apps E} {p : Participant} {T : Threat E p}
    (B : Bounds apps p T) (net : Nitro.ReachableParticipant apps T) :
    ∀ ss ∈ net.state.received, net.state.Unforged ss := by
  obtain_reach ⟨net, h⟩ := net
  refine Machine.invariant (Nitro.participant apps T)
    (P := fun net => ∀ ss ∈ net.received, net.Unforged ss) ?_ ?_ net h
  · intro net hinit ss hss
    rw [hinit] at hss
    exact absurd hss (List.not_mem_nil)
  · intro net net' hP hstep
    rcases hstep with ⟨m, hm, rfl⟩ | ⟨op, hop, rfl⟩ | ⟨m, hm, hnoland, rfl⟩ | ⟨a, e, x, rfl⟩
    · intro ss hss
      have hsent : net.sent ⊆ (net.applyHonest m).sent := by
        cases m with
        | react r =>
          intro x hx
          simp only [NetworkState.applyHonest, List.mem_append]
          exact Or.inr hx
        | wait dt => (simp? [NetworkState.applyHonest] says simp only [NetworkState.applyHonest, List.Subset.refl])
      have hrecv : (net.applyHonest m).received = net.received := by
        cases m with
        | react r => rfl
        | wait dt => rfl
      rw [hrecv] at hss
      exact NetworkState.Unforged.mono hsent (hP ss hss)
    · have hsent : net.sent = (net.applyAdv apps (.land op)).sent := by
        cases hap : net.chain.apply apps p op with
        | none => (simp? [NetworkState.applyAdv, hap] says simp only [NetworkState.applyAdv, hap])
        | some s' => (simp? [NetworkState.applyAdv, hap] says simp only [NetworkState.applyAdv, hap])
      intro ss hss
      cases hap : net.chain.apply apps p op with
      | none =>
        simp only [NetworkState.applyAdv, hap] at hss
        exact NetworkState.Unforged.of_sent hsent (hP ss hss)
      | some s' =>
        simp only [NetworkState.applyAdv, hap, List.mem_append] at hss
        rcases hss with hss | hss
        · exact NetworkState.Unforged.of_sent hsent
            (NetworkState.Holds.unforged (Op.HonestFeasible.mem hop ss hss) hP)
        · exact NetworkState.Unforged.of_sent hsent (hP ss hss)
    · have hsent : net.sent = (net.applyAdv apps m).sent := by
        cases m with
        | chain caller op =>
          cases hap : net.chain.apply apps caller op with
          | none => (simp? [NetworkState.applyAdv, hap] says simp only [NetworkState.applyAdv, hap])
          | some s' => (simp? [NetworkState.applyAdv, hap] says simp only [NetworkState.applyAdv, hap])
        | deliver ss' => (simp? [NetworkState.applyAdv] says simp only [NetworkState.applyAdv])
        | tick dt => (simp? [NetworkState.applyAdv] says simp only [NetworkState.applyAdv])
        | land op => exact absurd rfl (hnoland op)
      intro ss hss
      cases m with
      | chain caller op =>
        cases hap : net.chain.apply apps caller op with
        | none =>
          simp only [NetworkState.applyAdv, hap] at hss
          exact NetworkState.Unforged.of_sent hsent (hP ss hss)
        | some s' =>
          simp only [NetworkState.applyAdv, hap, List.mem_append] at hss
          rcases hss with hss | hss
          · exact NetworkState.Unforged.of_sent hsent (B.unforgeable net caller op hm ss hss)
          · exact NetworkState.Unforged.of_sent hsent (hP ss hss)
      | deliver ss' =>
        simp only [NetworkState.applyAdv, List.mem_cons] at hss
        rcases hss with heq | hss
        · rw [heq]
          exact NetworkState.Unforged.of_sent hsent (B.unforgeableDeliver net ss' hm)
        · exact NetworkState.Unforged.of_sent hsent (hP ss hss)
      | tick dt =>
        simp only [NetworkState.applyAdv] at hss
        exact NetworkState.Unforged.of_sent hsent (hP ss hss)
      | land op => exact absurd rfl (hnoland op)
    · have hsent : net.sent = (net.applyAdv apps (.land (.deposit a e x))).sent := by
        cases hap : net.chain.apply apps p (.deposit a e x) with
        | none => (simp? [NetworkState.applyAdv, hap] says simp only [NetworkState.applyAdv, hap])
        | some s' => (simp? [NetworkState.applyAdv, hap] says simp only [NetworkState.applyAdv, hap])
      intro ss hss
      cases hap : net.chain.apply apps p (.deposit a e x) with
      | none =>
        simp only [NetworkState.applyAdv, hap] at hss
        exact NetworkState.Unforged.of_sent hsent (hP ss hss)
      | some s' =>
        simp only [NetworkState.applyAdv, hap, Op.proofStates, List.nil_append] at hss
        exact NetworkState.Unforged.of_sent hsent (hP ss hss)

/-- An adversary move keeps `p`'s `sent` and only grows `p`'s `received`
    (`NetworkState.applyAdv`'s per-move effect lemmas, `Strategy.lean`). -/
theorem NetworkState.applyAdv_sent_received (apps : Apps E) {p : Participant}
    (net : NetworkState E p) (m : AdvMove E) :
    (net.applyAdv apps m).sent = net.sent ∧ ∀ r ∈ net.received, r ∈ (net.applyAdv apps m).received := by
  cases m with
  | chain caller op =>
    cases h : net.chain.apply apps caller op with
    | none => rw [NetworkState.applyAdv_chain_none apps h]; exact ⟨rfl, fun _ hr => hr⟩
    | some s' =>
      rw [NetworkState.applyAdv_chain_some apps h]
      exact ⟨rfl, fun _ hr => List.mem_append_right _ hr⟩
  | deliver ss =>
    rw [NetworkState.applyAdv_deliver]
    exact ⟨rfl, fun _ hr => List.mem_cons_of_mem _ hr⟩
  | tick dt => rw [NetworkState.applyAdv_tick]; exact ⟨rfl, fun _ hr => hr⟩
  | land op =>
    cases h : net.chain.apply apps p op with
    | none => rw [NetworkState.applyAdv_land_none apps h]; exact ⟨rfl, fun _ hr => hr⟩
    | some s' =>
      rw [NetworkState.applyAdv_land_some apps h]
      exact ⟨rfl, fun _ hr => List.mem_append_right _ hr⟩

/-- **Every state the honest `p` signed satisfies the signing rules**
    (`HonestSend`, `ArmadaLean/Types/Honest.lean`, option A of
    2026-11-01): against every state `p` signed, and with the
    pre-fund states and the supports `p` holds now
    (`NetworkState.HoldsPrefund`, `NetworkState.CanMoveTo`). By
    `Machine.invariant`. The initial `sent` is empty. A `.react` adds only
    sends that its gate (`Reaction.SendsHonest`, part of
    `HonestMove.Feasible`) checks against the new `sent`. An old state's
    `noConflict` against a new send is the new send's own
    `noConflict`, read in the other direction. Every other step keeps `sent` and only grows `received`
    (`NetworkState.applyAdv_sent_received`), so the held pre-fund states and
    supports survive (`NetworkState.held_mono`, `NetworkState.Holds.of_subset`). -/
theorem Nitro.participant_sent_honest {apps : Apps E} {p : Participant} {T : Threat E p}
    (net : Nitro.ReachableParticipant apps T) :
    ∀ s ∈ net.state.sent, HonestSend net.state.sent net.state.HoldsPrefund
      (net.state.CanMoveTo apps) s.state := by
  obtain_reach ⟨net, h⟩ := net
  refine Machine.invariant (Nitro.participant apps T)
    (P := fun net => ∀ s ∈ net.sent, HonestSend net.sent net.HoldsPrefund
      (net.CanMoveTo apps) s.state) ?_ ?_ net h
  · intro net hinit s hs
    rw [hinit] at hs
    exact absurd hs List.not_mem_nil
  · intro net net' hP hstep
    have keep : ∀ net' : NetworkState E p, net'.sent = net.sent →
        (∀ r ∈ net.received, r ∈ net'.received) →
        ∀ s ∈ net'.sent, HonestSend net'.sent net'.HoldsPrefund (net'.CanMoveTo apps) s.state := by
      intro net' hs hr s hmem
      rw [hs] at hmem
      have hsub : ∀ x ∈ net.sent, x ∈ net'.sent := fun x hx => hs ▸ hx
      rw [hs]
      have hm := NetworkState.held_mono (apps := apps) fun _ h => h.of_subset hsub hr
      exact (hP s hmem).mono (fun _ hx => hx) hm.1 hm.2
    rcases hstep with ⟨m, hm, rfl⟩ | ⟨op, -, rfl⟩ | ⟨m, -, -, rfl⟩ | ⟨a, e, x, rfl⟩
    · cases m with
      | react r =>
        have hsends : r.SendsHonest apps net := hm.2
        have hsub : ∀ x ∈ net.sent, x ∈ (net.applyHonest (.react r)).sent :=
          fun x hx => List.mem_append_right _ hx
        obtain ⟨hheld, hsup⟩ := NetworkState.held_mono (apps := apps)
          (net' := net.applyHonest (.react r)) fun _ h => h.of_subset hsub (fun _ hx => hx)
        intro s hs
        change s ∈ r.sends.map (fun st => (⟨st, [p]⟩ : SignedState E)) ++ net.sent at hs
        change HonestSend (r.sends.map (fun st => (⟨st, [p]⟩ : SignedState E)) ++ net.sent)
          (net.applyHonest (.react r)).HoldsPrefund ((net.applyHonest (.react r)).CanMoveTo apps)
          s.state
        rcases List.mem_append.mp hs with hnew | hold
        · obtain ⟨st, hst, rfl⟩ := List.mem_map.mp hnew
          exact (hsends st hst).mono (fun _ hx => hx) hheld hsup
        · have hs0 := hP s hold
          refine ⟨fun ⟨t, ht, hc, hslot, hne⟩ => ?_, hs0.guaranteesExternal,
            fun V hV hf => hheld V (hs0.fundsCommitted V hV hf), fun hn => hsup _ (hs0.movesFrom hn),
            fun ⟨t, ht, hc, htn, hne⟩ => ?_, fun ⟨t, ht, hc, hfb⟩ => ?_⟩
          · rcases List.mem_append.mp ht with htnew | htold
            · obtain ⟨st, hst, rfl⟩ := List.mem_map.mp htnew
              exact hne ((hsends st hst).outcome_eq _ hs hc.symm hslot.symm).symm
            · exact hne ((hP s hold).outcome_eq _ htold hc hslot)
          · rcases List.mem_append.mp ht with htnew | htold
            · obtain ⟨st, hst, rfl⟩ := List.mem_map.mp htnew
              exact (hsends st hst).oneState ⟨s, hs, hc.symm, htn.symm, Ne.symm hne⟩
            · exact hs0.oneState ⟨t, htold, hc, htn, hne⟩
          · rcases List.mem_append.mp ht with htnew | htold
            · obtain ⟨st, hst, rfl⟩ := List.mem_map.mp htnew
              exact (hsends st hst).finalLast ⟨s, hs, hc.symm, hfb.symm⟩
            · exact hs0.finalLast ⟨t, htold, hc, hfb⟩
      | wait dt => exact keep _ rfl (fun _ hx => hx)
    · exact keep _ (NetworkState.applyAdv_sent_received apps net (.land op)).1
        (NetworkState.applyAdv_sent_received apps net (.land op)).2
    · exact keep _ (NetworkState.applyAdv_sent_received apps net m).1
        (NetworkState.applyAdv_sent_received apps net m).2
    · exact keep _ (NetworkState.applyAdv_sent_received apps net (.land (.deposit a e x))).1
        (NetworkState.applyAdv_sent_received apps net (.land (.deposit a e x))).2

/-- **A state that the honest `p` holds with its own signature satisfies the
    signing rules.** `p`'s signature on a held state is on a state `p` sent
    (`NetworkState.Holds.unforged`, `Nitro.participant_received_unforged`), and
    that sent state satisfies `HonestSend` (`Nitro.participant_sent_honest`). -/
theorem Nitro.participant_holds_honest {apps : Apps E} {p : Participant} {T : Threat E p}
    (B : Bounds apps p T) (net : Nitro.ReachableParticipant apps T) {ss : SignedState E}
    (hH : net.state.Holds ss) (hp : p ∈ ss.signers) :
    HonestSend net.state.sent net.state.HoldsPrefund (net.state.CanMoveTo apps) ss.state := by
  obtain ⟨s, hs, heq⟩ := (hH.unforged (Nitro.participant_received_unforged B net)).1 hp
  rw [← heq]
  exact Nitro.participant_sent_honest net s hs

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
  /-- Each participant's own coins, outside the chain ("D10: no deposits in network histories; wallets":
      "participants cannot create coins, but they bring their own
      balances of arbitrary size"). `Nitro.network.init` leaves `wallet`
      unconstrained; `Network.deposit` is the only step that reads or
      writes it, moving `x` from `wallet p` to a ledger channel
      (Nitro:395-398: "where the channel ... has enough coins in the
      adjudicator ... In this case, we say the channel is directly
      funded", funding by deposit before any strategy runs). -/
  wallet : Participant → Coins

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
    reach the sender's own `sent`, and, in the same step (synchronous network), every recipient's `received`
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
    (simp? [State.recipients, List.mem_filter] says simp only [State.recipients, ne_eq, decide_not, List.mem_filter, decide_true, Bool.not_true, Bool.false_eq_true, and_false, decide_false, not_false_eq_true])
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
  | some s' =>
    { n with chain := s', received := fun q => op.proofStates ++ n.received q }
  | none => n

/-- `p` deposits `x` of its own wallet into address `a` ("D10: no deposits in network histories; wallets":
    "participants cannot create coins, but they bring their own balances
    of arbitrary size... a deposit (into a ledger channel only) debits
    the depositor's wallet"). Nitro:395-398 funds a channel by deposit
    before any strategy runs; a deposit is `Op.HonestFeasible`-excluded
    (D3, `Strategy.lean:120`), so it is a machine step here, not a
    reaction a strategy issues (`Nitro.network`'s own step, below).
    `Adjudicator.deposit` already refuses a non-ledger address and a
    mismatched `expectedHeld`; a refusal leaves `n` entirely unchanged,
    the depositor's wallet included, the same "changes nothing" shape as
    `Network.land`'s own failed call. -/
def Network.deposit (n : Network E) (p : Participant) (a : Address E) (expectedHeld x : Coins) :
    Network E :=
  match n.chain.deposit a expectedHeld x with
  | some s' =>
    { n with
      chain := s'
      wallet := fun q => if q = p then n.wallet p - x else n.wallet q }
  | none => n

@[simp] theorem Network.deposit_sent (n : Network E) (p : Participant) (a : Address E)
    (expectedHeld x : Coins) (q : Participant) :
    (Network.deposit n p a expectedHeld x).sent q = n.sent q := by
  simp only [Network.deposit]
  cases n.chain.deposit a expectedHeld x <;> rfl

@[simp] theorem Network.deposit_received (n : Network E) (p : Participant) (a : Address E)
    (expectedHeld x : Coins) (q : Participant) :
    (Network.deposit n p a expectedHeld x).received q = n.received q := by
  simp only [Network.deposit]
  cases n.chain.deposit a expectedHeld x <;> rfl

/-- One adversary move against `p`, applied to the whole `Network`
    (`NetworkState.applyAdv`, read from `p`'s view). `.deliver ss` reaches
    only `p`'s own `received`: the per-participant model alone does not
    forbid delivering a forged OTHER signer's claim
    (`Bounds.unforgeable`/`NetworkState.Unforged` bound only `p`'s own
    alleged signature, by design, `Strategy.lean`), so `Nitro.network`'s
    step additionally requires `Network.Sendable ss`. The caller rule
    excludes `.chain` and `.land` from the
    adversary's own moves at the `Nitro.network` step (below); this
    function still accepts them, for the single-view lemmas that reuse
    it with an explicit caller/landing participant. Design decision
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
  | .chain caller op => Network.land apps n caller op
  | .deliver ss => { n with received := fun q => if q = p then ss :: n.received q else n.received q }
  | .tick dt => { n with chain := n.chain.tick dt }
  | .land op => Network.land apps n p op

/-- `Network.land` when the call succeeds (`writing-lean.md` rule 3). -/
@[simp] theorem Network.land_of_some {apps : Apps E} {n : Network E} {p : Participant} {op : Op E}
    {s' : Adjudicator E} (h : n.chain.apply apps p op = some s') :
    Network.land apps n p op = { n with chain := s', received := fun q => op.proofStates ++ n.received q } := by
  (simp? [Network.land, h] says simp only [land, h])

/-- `Network.land` when the call fails: nothing changes. -/
@[simp] theorem Network.land_of_none {apps : Apps E} {n : Network E} {p : Participant} {op : Op E}
    (h : n.chain.apply apps p op = none) : Network.land apps n p op = n := by
  (simp? [Network.land, h] says simp only [land, h])


@[simp] theorem Network.applyAdv_chain (apps : Apps E) (n : Network E) (p caller : Participant) (op : Op E) :
    Network.applyAdv apps n p (.chain caller op) = Network.land apps n caller op := by
  rfl

@[simp] theorem Network.applyAdv_deliver (apps : Apps E) (n : Network E) (p : Participant) (ss : SignedState E) :
    Network.applyAdv apps n p (.deliver ss) =
      { n with received := fun q => if q = p then ss :: n.received q else n.received q } := by
  rfl

@[simp] theorem Network.applyAdv_tick (apps : Apps E) (n : Network E) (p : Participant) (dt : Time) :
    Network.applyAdv apps n p (.tick dt) = { n with chain := n.chain.tick dt } := by
  rfl

@[simp] theorem Network.applyAdv_land (apps : Apps E) (n : Network E) (p : Participant) (op : Op E) :
    Network.applyAdv apps n p (.land op) = Network.land apps n p op := by
  rfl

theorem Network.applyHonest_chain_reachable {apps : Apps E} (n : Network E) (p : Participant)
    (m : HonestMove E) (hr : Reachable apps n.chain) :
    Reachable apps (Network.applyHonest n p m).chain := by
  cases m with
  | react r => (simpa? using hr says simpa only [applyHonest_react_chain] using hr)
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

theorem Network.deposit_chain_reachable {apps : Apps E} (n : Network E) (p : Participant)
    (a : Address E) (expectedHeld x : Coins) (hr : Reachable apps n.chain) :
    Reachable apps (Network.deposit n p a expectedHeld x).chain := by
  simp only [Network.deposit]
  cases h : n.chain.deposit a expectedHeld x with
  | none => exact hr
  | some s' => exact hr.tail (Step.mk p (.deposit a expectedHeld x) n.chain s' h)

theorem Network.applyAdv_chain_reachable {apps : Apps E} (n : Network E) (p : Participant)
    (m : AdvMove E) (hr : Reachable apps n.chain) :
    Reachable apps (Network.applyAdv apps n p m).chain := by
  cases m with
  | chain caller op =>
    simp only [Network.applyAdv_chain, Network.land]
    cases h : n.chain.apply apps caller op with
    | none => exact hr
    | some s' => exact hr.tail (Step.mk caller op n.chain s' h)
  | deliver ss => (simpa? [Network.applyAdv_deliver] using hr says simpa only [applyAdv_deliver] using hr)
  | tick dt =>
    simp only [Network.applyAdv_tick]
    have happly : n.chain.apply apps p (.tick dt) = some (n.chain.tick dt) := rfl
    exact hr.tail (Step.mk p (.tick dt) n.chain (n.chain.tick dt) happly)
  | land op => exact Network.land_chain_reachable n p op hr

/-- The network game, with each honest step gated by `honest`: at each step,
    some participant `p` makes one of its own honest moves that `honest`
    allows (`Nitro.network` gates it by `HonestMove.Feasible`; a reaction's
    sends only, calls land
    separately below), `p` lands one of its own currently-feasible calls
    (`Network.land`, gated by `Network.Sendable` on its proof states, the
    same public-broadcast fact the old `.chain` gate stated), `p`'s own
    adversary `Ts.T p` makes one feasible `.deliver`/`.tick` move against
    `p`, or `p` deposits some of its own wallet into a ledger channel
    (`Network.deposit`, D10 design decision). `Network.Sendable` gates a `.deliver`
    and every landed call's proof states: SATP:168 "forging cryptographic
    signatures is infeasible" is a system-wide fact, already encoded on
    the chain side by `ReachableSigned`'s own hypothesis
    (`Adjudicator.lean`, `SignedStep`'s `hsig`); this is the same fact for
    the network's own `sent` record, so every signature a proof state
    carries is genuine, not only the acting view's own. The caller rule
    (the "Caller rule",
    read literally): "only q's own honest moves may
    submit an on-chain call with caller q" — for every participant, not
    only a channel's, and (explicit-time addendum) the same for landing:
    only `q`'s own call ever lands with caller `q`. An adversary move is
    never a `.chain` or `.land` move at all, so the adversary's moves are
    only `.deliver` and `.tick`. Design decision 2026-10-29:
    `ReachableViews` is `(Nitro.network apps Ts).Reachable`, not a separate
    predicate. A second gate, `Network.VoucherSendable`, covers the one
    part of `Network.Sendable` a first send cannot satisfy of itself (that
    definition's doc comment). D10 design decision (2026-10-29, "D10: no deposits
    in network histories; wallets"): "participants cannot create coins,
    but they bring their own balances of arbitrary size. Each participant
    has a wallet. The machines' initial state gives each wallet an
    arbitrary amount, and a deposit ... debits the depositor's wallet.
    Histories admit deposits; honest strategies keep D3." `init` leaves
    `wallet` unconstrained (any initial amount); `wallet` moves only
    through a deposit (`Network.deposit`), never through an honest
    strategy move (`Op.HonestFeasible` still rejects `.deposit`, D3,
    `Strategy.lean:120`) and never through any other adversary move (only
    this disjunct reads or writes `wallet`). -/
def Nitro.networkWith (apps : Apps E) (Ts : Threats E apps)
    (honest : ∀ p : Participant, NetworkState E p → HonestMove E → Prop) : Machine (Network E) where
  init := fun n => n.chain = Adjudicator.genesis ∧ n.sent = (fun _ => []) ∧ n.received = (fun _ => [])
  step := fun n n' => ∃ p : Participant,
    (∃ m : HonestMove E, honest p (n.view p) m ∧
      (∀ r : Reaction E, m = .react r → ∀ st ∈ r.sends, n.VoucherSendable st) ∧
      n' = Network.applyHonest n p m) ∨
    (∃ op : Op E, op.HonestFeasible (n.view p) ∧
      (∀ ss ∈ op.proofStates, n.Sendable ss) ∧
      n' = Network.land apps n p op) ∨
    (∃ m : AdvMove E, (Ts.T p).feasible (n.view p) m ∧
      (∀ ss, m = .deliver ss → n.Sendable ss) ∧
      (∀ caller op, m ≠ .chain caller op) ∧ (∀ op, m ≠ .land op) ∧
      n' = Network.applyAdv apps n p m) ∨
    (∃ c : FixedPart, ∃ e x : Coins, x ≤ n.wallet p ∧ n' = Network.deposit n p (.channel c) e x)

/-- The network game (`Nitro.networkWith`): an honest move must be feasible
    (`HonestMove.Feasible`), so every send satisfies the signing rules of
    `HonestSend` (`Types/Honest.lean`, option A). -/
def Nitro.network (apps : Apps E) (Ts : Threats E apps) : Machine (Network E) :=
  Nitro.networkWith apps Ts (fun _ net m => m.Feasible apps net)

/-- The network game with no signing rule: an honest move needs only
    feasible calls (`HonestMove.CallsFeasible`). Only counterexamples that
    need a participant that signs against `HonestSend` use it
    (`docs/counterexamples/`, each with its own reachability steps); no
    declaration of the library is stated over it. -/
def Nitro.networkUnrestricted (apps : Apps E) (Ts : Threats E apps) : Machine (Network E) :=
  Nitro.networkWith apps Ts (fun _ net m => m.CallsFeasible net)

/-- The reachable states of the network game (`Nitro.network`), as a type
    (`ArmadaLean/Types/Reachable.lean`; operator decision 2026-10-31). -/
abbrev Nitro.ReachableNetwork (apps : Apps E) (Ts : Threats E apps) : Type :=
  ReachableState (Nitro.network apps Ts)

/-- **The chain of a reachable `Network` is reachable.** By
    `Machine.invariant`, using `Network.applyHonest_chain_reachable` /
    `Network.land_chain_reachable` / `Network.applyAdv_chain_reachable` for
    the step case. -/
theorem Nitro.network_chain_reachable {apps : Apps E} {Ts : Threats E apps} {n : Network E}
    (h : (Nitro.network apps Ts).Reachable n) : Reachable apps n.chain := by
  refine Machine.invariant (Nitro.network apps Ts) (P := fun n => Reachable apps n.chain) ?_ ?_ n h
  · intro n hinit
    obtain ⟨hc, -, -⟩ := hinit
    rw [hc]
    exact Relation.ReflTransGen.refl
  · intro n n' hP hstep
    obtain ⟨p, ⟨m, -, -, rfl⟩ | ⟨op, -, -, rfl⟩ | ⟨m, -, -, -, -, rfl⟩ | ⟨c, e, x, -, rfl⟩⟩ := hstep
    · exact Network.applyHonest_chain_reachable n p m hP
    · exact Network.land_chain_reachable n p op hP
    · exact Network.applyAdv_chain_reachable n p m hP
    · exact Network.deposit_chain_reachable n p (.channel c) e x hP

/-- **How one `Nitro.network` step changes `(chain, sent, received, wallet)`.**
    One level deeper than `Nitro.network`'s own step relation (above): an
    honest move is a `.react` (only the sender's own `sent` and the
    recipients' `received` grow, gated `VoucherSendable`) or a `.wait` (only
    `chain` ticks); landing a call either fails (`n' = n`) or succeeds
    (`chain` advances, every `received` gains the call's proof states, gated
    `Sendable`, and the mover's own feasibility excludes a landed `op` ever
    being a deposit); the adversary's own moves are only `.deliver` (gated
    `Sendable`, only the acting participant's `received` grows) and `.tick`
    (only `chain` ticks), by the caller rule (`hnochain`/`hnoland`); a
    deposit either fails (`n' = n`) or succeeds (`chain` advances, only the
    depositor's `wallet` falls, by at most its own balance). Combines the
    already-proved per-field simp lemmas
    (`Network.applyHonest_react_sent`/`_received`, `Network.land_of_none`/
    `_of_some`, `Network.applyAdv_deliver`/`_tick`,
    `Network.deposit_sent`/`_received`), so a consumer states its step case
    once, not once per field per branch (`writing-lean.md` §6). The two
    "nothing changes" shapes (a failed landed call, a failed deposit) and
    the two "only `chain` ticks" shapes (`.wait`, adversary `.tick`) collapse
    to one branch each: every known consumer treats them alike. -/
theorem Nitro.network.step_frame {apps : Apps E} {Ts : Threats E apps} {n n' : Network E}
    (hstep : (Nitro.network apps Ts).step n n') :
    ∃ p₀ : Participant,
      (∃ r : Reaction E, (∀ st ∈ r.sends, n.VoucherSendable st) ∧
        n'.chain = n.chain ∧
        n'.sent = (fun q => if q = p₀ then
          r.sends.map (fun st => (⟨st, [p₀]⟩ : SignedState E)) ++ n.sent q else n.sent q) ∧
        n'.received = (fun q =>
          (r.sends.filter (fun st => decide (q ∈ st.recipients p₀))).map
            (fun st => (⟨st, [p₀]⟩ : SignedState E)) ++ n.received q) ∧
        n'.wallet = n.wallet) ∨
      (∃ dt : Time, n'.chain = n.chain.tick dt ∧ n'.sent = n.sent ∧
        n'.received = n.received ∧ n'.wallet = n.wallet) ∨
      n' = n ∨
      (∃ (op : Op E) (s' : Adjudicator E), op.HonestFeasible (n.view p₀) ∧
        n.chain.apply apps p₀ op = some s' ∧ (∀ ss ∈ op.proofStates, n.Sendable ss) ∧
        n'.chain = s' ∧ n'.sent = n.sent ∧
        n'.received = (fun q => op.proofStates ++ n.received q) ∧ n'.wallet = n.wallet) ∨
      (∃ ss : SignedState E, n.Sendable ss ∧
        n'.chain = n.chain ∧ n'.sent = n.sent ∧
        n'.received = (fun q => if q = p₀ then ss :: n.received q else n.received q) ∧
        n'.wallet = n.wallet) ∨
      (∃ (c : FixedPart) (e x : Coins) (s' : Adjudicator E), x ≤ n.wallet p₀ ∧
        n.chain.deposit (.channel c) e x = some s' ∧
        n'.chain = s' ∧ n'.sent = n.sent ∧ n'.received = n.received ∧
        n'.wallet = (fun q => if q = p₀ then n.wallet p₀ - x else n.wallet q)) := by
  obtain ⟨p₀, ⟨m, -, hvgate, rfl⟩ | ⟨op, hfeas, hsgate, rfl⟩ |
      ⟨m, -, hdgate, hnochain, hnoland, rfl⟩ | ⟨c, e, x, hxle, rfl⟩⟩ := hstep
  · refine ⟨p₀, ?_⟩
    cases m with
    | react r => exact Or.inl ⟨r, hvgate r rfl, rfl, rfl, rfl, rfl⟩
    | wait dt => exact Or.inr (Or.inl ⟨dt, rfl, rfl, rfl, rfl⟩)
  · refine ⟨p₀, ?_⟩
    cases hop : n.chain.apply apps p₀ op with
    | none => exact Or.inr (Or.inr (Or.inl (Network.land_of_none hop)))
    | some s' =>
      refine Or.inr (Or.inr (Or.inr (Or.inl ⟨op, s', hfeas, hop, hsgate, ?_, ?_, ?_, ?_⟩))) <;>
        simp only [Network.land_of_some hop]
  · refine ⟨p₀, ?_⟩
    cases m with
    | chain caller op => exact absurd rfl (hnochain caller op)
    | deliver ss =>
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨ss, hdgate ss rfl, rfl, rfl, rfl, rfl⟩))))
    | tick dt => exact Or.inr (Or.inl ⟨dt, rfl, rfl, rfl, rfl⟩)
    | land op => exact absurd rfl (hnoland op)
  · refine ⟨p₀, ?_⟩
    cases hdep : n.chain.deposit (.channel c) e x with
    | none => exact Or.inr (Or.inr (Or.inl (by simp only [Network.deposit, hdep])))
    | some s' =>
      refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        ⟨c, e, x, s', hxle, hdep, ?_, ?_, ?_, ?_⟩)))) <;>
        simp only [Network.deposit, hdep]

/-- **Every signature a view received is genuine, in every reachable
    `Network`.** A state `p` received that names `q` as a signer is a
    state `q` really sent. `p` and `q` can be one participant: `p`'s own
    signature on a state `p` received is on a state `p` sent. By
    `Machine.invariant`: at genesis every `received` is empty (vacuous); a
    step leaves `received` untouched (`wait`), touches only the mover's own
    `received` through a `Network.Sendable`-gated `.deliver` (whose
    statement is exactly this fact for the one new entry), broadcasts a
    landed call's `Network.Sendable`-gated proof states (same argument, for
    every new entry at once), or appends a `.react`'s one-shot recipient
    batch, each new entry's own signer `p₀` already known-genuine by `hP`.
    Used by `finalizable_unique` (`Liveness.lean`), whose joint play needs
    the case `p = q` too. -/
theorem Nitro.network_received_signers {apps : Apps E} {Ts : Threats E apps} {n : Network E}
    (h : (Nitro.network apps Ts).Reachable n) :
    ∀ p q : Participant, ∀ r ∈ (n.views p).received, q ∈ r.signers →
      ∃ s ∈ (n.views q).sent, s.state = r.state := by
  refine Machine.invariant (Nitro.network apps Ts)
    (P := fun n => ∀ p q : Participant, ∀ r ∈ n.received p, q ∈ r.signers →
      ∃ s ∈ n.sent q, s.state = r.state) ?_ ?_ n h
  · intro n hinit p q r hr
    obtain ⟨-, -, hrecv⟩ := hinit
    rw [hrecv] at hr
    (simp? at hr says simp only [List.not_mem_nil] at hr)
  · intro n n' hP hstep p q r hr hqr
    obtain ⟨p₀, hframe⟩ := Nitro.network.step_frame hstep
    rcases hframe with
        ⟨rr, -, -, hsent, hrecv, -⟩ | ⟨dt, -, hsent, hrecv, -⟩ | hunchanged |
        ⟨op, s', -, -, hsgate, -, hsent, hrecv, -⟩ | ⟨ss, hgate, -, hsent, hrecv, -⟩ |
        ⟨c, e, x, s', -, -, -, hsent, hrecv, -⟩
    · simp only [hrecv] at hr
      rw [List.mem_append] at hr
      rcases hr with hnew | hold
      · obtain ⟨st, hst, hseq⟩ := List.mem_map.mp hnew
        obtain ⟨hst', -⟩ := List.mem_filter.mp hst
        rw [← hseq] at hqr
        simp only [List.mem_singleton] at hqr
        refine ⟨⟨st, [p₀]⟩, ?_, by rw [← hseq]⟩
        simp only [hsent, if_pos hqr]
        exact List.mem_append_left _ (List.mem_map.mpr ⟨st, hst', rfl⟩)
      · obtain ⟨s, hs, hseq⟩ := hP p q r hold hqr
        refine ⟨s, ?_, hseq⟩
        simp only [hsent]
        by_cases hqp0 : q = p₀
        · rw [if_pos hqp0]; exact List.mem_append_right _ hs
        · rw [if_neg hqp0]; exact hs
    · rw [hsent]
      rw [hrecv] at hr
      exact hP p q r hr hqr
    · subst hunchanged
      exact hP p q r hr hqr
    · simp only [hrecv] at hr
      rw [hsent]
      rcases List.mem_append.mp hr with hnew | hold
      · exact (hsgate r hnew).1 q hqr
      · exact hP p q r hold hqr
    · rw [hsent]
      simp only [hrecv] at hr
      by_cases hpp0 : p = p₀
      · rw [if_pos hpp0] at hr
        rcases List.mem_cons.mp hr with rfl | hold
        · exact hgate.1 q hqr
        · exact hP p q r hold hqr
      · rw [if_neg hpp0] at hr
        exact hP p q r hr hqr
    · rw [hsent]
      rw [hrecv] at hr
      exact hP p q r hr hqr

/-- **Every voucher signature (SATP:703, SATP:630-637) a view's received state carries is
    genuine, in every reachable `Network`.** If `r`, received by `p`,
    carries a voucher `v` naming `q` as a signer, `q` sent some state that
    carries the same voucher `v`. By `Machine.invariant`, same shape as
    `Nitro.network_received_signers`: at genesis every `received` is
    empty; a step leaves `received` untouched (`wait`), touches only the
    mover's own `received` through a gated move whose gate's voucher
    clause (`Network.Sendable.2`, `Network.VoucherSendable`) is exactly
    this fact for the one or more new entries, or carries the invariant
    forward for an old entry. Used by `finalizable_unique` (`Liveness.lean`,
    D7 voucher rule repaired; see
    the funding-point alternative-moves analysis. -/
theorem Nitro.network_received_voucher_signers {apps : Apps E} {Ts : Threats E apps} (n : Nitro.ReachableNetwork apps Ts)
    :
    ∀ p q : Participant, ∀ r ∈ (n.state.views p).received, ∀ v, r.state.voucher? = some v → q ∈ v.signers →
      ∃ s ∈ (n.state.views q).sent, s.state.voucher? = some v := by
  obtain_reach ⟨n, h⟩ := n
  refine Machine.invariant (Nitro.network apps Ts)
    (P := fun n => ∀ p q : Participant, ∀ r ∈ n.received p, ∀ v, r.state.voucher? = some v →
      q ∈ v.signers → ∃ s ∈ n.sent q, s.state.voucher? = some v) ?_ ?_ n h
  · intro n hinit p q r hr
    obtain ⟨-, -, hrecv⟩ := hinit
    rw [hrecv] at hr
    (simp? at hr says simp only [List.not_mem_nil] at hr)
  · intro n n' hP hstep p q r hr v hv hq
    obtain ⟨p₀, hframe⟩ := Nitro.network.step_frame hstep
    rcases hframe with
        ⟨rr, hvgate, -, hsent, hrecv, -⟩ | ⟨dt, -, hsent, hrecv, -⟩ | hunchanged |
        ⟨op, s', -, -, hsgate, -, hsent, hrecv, -⟩ | ⟨ss, hgate, -, hsent, hrecv, -⟩ |
        ⟨c, e, x, s', -, -, -, hsent, hrecv, -⟩
    · simp only [hrecv] at hr
      rw [List.mem_append] at hr
      rcases hr with hnew | hold
      · obtain ⟨st, hst, hseq⟩ := List.mem_map.mp hnew
        obtain ⟨hst', -⟩ := List.mem_filter.mp hst
        rw [← hseq] at hv
        obtain ⟨s, hs, hse⟩ := hvgate st hst' v hv q hq
        refine ⟨s, ?_, hse⟩
        simp only [hsent]
        by_cases hqp0 : q = p₀
        · rw [if_pos hqp0]; exact List.mem_append_right _ hs
        · rw [if_neg hqp0]; exact hs
      · obtain ⟨s, hs, hse⟩ := hP p q r hold v hv hq
        refine ⟨s, ?_, hse⟩
        simp only [hsent]
        by_cases hqp0 : q = p₀
        · rw [if_pos hqp0]; exact List.mem_append_right _ hs
        · rw [if_neg hqp0]; exact hs
    · rw [hsent]
      rw [hrecv] at hr
      exact hP p q r hr v hv hq
    · subst hunchanged
      exact hP p q r hr v hv hq
    · simp only [hrecv] at hr
      rw [hsent]
      rcases List.mem_append.mp hr with hnew | hold
      · exact (hsgate r hnew).2 v hv q hq
      · exact hP p q r hold v hv hq
    · rw [hsent]
      simp only [hrecv] at hr
      by_cases hpp0 : p = p₀
      · rw [if_pos hpp0] at hr
        rcases List.mem_cons.mp hr with rfl | hold
        · exact hgate.2 v hv q hq
        · exact hP p q r hold v hv hq
      · rw [if_neg hpp0] at hr
        exact hP p q r hr v hv hq
    · rw [hsent]
      rw [hrecv] at hr
      exact hP p q r hr v hv hq

/-- **`Views.Consistent`'s third conjunct holds for every reachable
    `Network`.** The case `p ≠ q` of `Nitro.network_received_signers`. -/
theorem Nitro.network_views_signers {apps : Apps E} {Ts : Threats E apps} {n : Network E}
    (h : (Nitro.network apps Ts).Reachable n) :
    ∀ p q : Participant, p ≠ q → ∀ r ∈ (n.views p).received, q ∈ r.signers →
      ∃ s ∈ (n.views q).sent, s.state = r.state :=
  fun p q _ => Nitro.network_received_signers h p q

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
    obtain ⟨hc, hs, -⟩ := hinit
    refine ⟨[], ?_, ?_⟩
    · rw [hc]; exact Relation.ReflTransGen.refl
    · intro q st; rw [hs]; (simp? says simp only [List.not_mem_nil, false_and, exists_false])
  · intro n n' hP hstep
    obtain ⟨signed, hreach, hmirror⟩ := hP
    obtain ⟨p₀, hframe⟩ := Nitro.network.step_frame hstep
    rcases hframe with
        ⟨rr, -, hchain, hsent, -, -⟩ | ⟨dt, hchain, hsent, -, -⟩ | hunchanged |
        ⟨op, s', -, hop, hsgate, hchain, hsent, -, -⟩ | ⟨ss, -, hchain, hsent, -, -⟩ |
        ⟨c, e, x, s', -, hdep, hchain, hsent, -, -⟩
    · refine ⟨rr.sends.map (fun st => (p₀, st)) ++ signed, ?_, ?_⟩
      · rw [hchain]
        simpa only using ReachableSigned.mono (fun x hx => List.mem_append_right _ hx) hreach
      · intro q st
        simp only [hsent, List.mem_append, List.mem_map]
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
    · refine ⟨signed, ?_, by rw [hsent]; exact hmirror⟩
      rw [hchain]
      refine hreach.tail ⟨p₀, .tick dt, _, _, ?_, rfl⟩
      simp only [Op.proofStates, List.not_mem_nil, IsEmpty.forall_iff, implies_true]
    · subst hunchanged
      exact ⟨signed, hreach, hmirror⟩
    · refine ⟨signed, ?_, by rw [hsent]; exact hmirror⟩
      rw [hchain]
      refine hreach.tail ⟨p₀, op, _, _, ?_, hop⟩
      intro ss hss
      obtain ⟨hsg, hvoucher⟩ := hsgate ss hss
      refine ⟨fun q' hq' => ?_, fun v hv q' hq' => ?_⟩
      · obtain ⟨s, hs', hseq⟩ := hsg q' hq'
        exact (hmirror q' ss.state).mpr ⟨s, hs', hseq⟩
      · obtain ⟨s, hs', hseq⟩ := hvoucher v hv q' hq'
        exact ⟨s.state, (hmirror q' s.state).mpr ⟨s, hs', rfl⟩, hseq⟩
    · exact ⟨signed, by rw [hchain]; exact hreach, by rw [hsent]; exact hmirror⟩
    · refine ⟨signed, ?_, by rw [hsent]; exact hmirror⟩
      rw [hchain]
      refine hreach.tail ⟨p₀, .deposit (.channel c) e x, _, _, ?_, hdep⟩
      intro ss hss
      simp only [Op.proofStates, List.not_mem_nil] at hss

/-- **`Views.Consistent`'s second conjunct holds for every reachable
    `Network`.** Design decision 2026-10-29: the network is synchronous by
    construction, so a state `p` sends reaches its recipients in the same
    step (`Network.applyHonest`'s `.react` arm). By `Machine.invariant`: at
    genesis every `sent` is empty (vacuous); a step leaves `sent`
    untouched except an honest `.react`, which both appends to the
    sender's own `sent` and, in the same step, to every recipient's
    `received`; every other move only ever grows `received`, for any
    participant, never removes from it, so a state already delivered to
    one of its recipients stays delivered. -/
theorem Nitro.network_views_delivered {apps : Apps E} {Ts : Threats E apps} (n : Nitro.ReachableNetwork apps Ts)
    :
    ∀ p, ∀ ss ∈ (n.state.views p).sent, ∀ q ∈ ss.state.recipients p, ss ∈ (n.state.views q).received := by
  obtain_reach ⟨n, h⟩ := n
  refine Machine.invariant (Nitro.network apps Ts)
    (P := fun n => ∀ p, ∀ ss ∈ n.sent p, ∀ q ∈ ss.state.recipients p, ss ∈ n.received q)
    ?_ ?_ n h
  · intro n hinit p ss hss
    obtain ⟨-, hs, -⟩ := hinit
    rw [hs] at hss
    (simp? at hss says simp only [List.not_mem_nil] at hss)
  · intro n n' hP hstep p ss hss q hq
    obtain ⟨p₀, hframe⟩ := Nitro.network.step_frame hstep
    rcases hframe with
        ⟨rr, -, -, hsent, hrecv, -⟩ | ⟨dt, -, hsent, hrecv, -⟩ | hunchanged |
        ⟨op, s', -, -, -, -, hsent, hrecv, -⟩ | ⟨ss', -, -, hsent, hrecv, -⟩ |
        ⟨c, e, x, s', -, -, -, hsent, hrecv, -⟩
    · simp only [hsent] at hss
      simp only [hrecv]
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
          simpa only [decide_eq_true_eq] using hq
        · rw [List.mem_append]
          exact Or.inr (hP p ss hold q hq)
      · rw [if_neg hpp0] at hss
        rw [List.mem_append]
        exact Or.inr (hP p ss hss q hq)
    · rw [hsent] at hss
      rw [hrecv]
      exact hP p ss hss q hq
    · subst hunchanged
      exact hP p ss hss q hq
    · rw [hsent] at hss
      simp only [hrecv]
      exact List.mem_append_right _ (hP p ss hss q hq)
    · rw [hsent] at hss
      simp only [hrecv]
      by_cases hqp0 : q = p₀
      · rw [if_pos hqp0]; exact List.mem_cons_of_mem _ (hP p ss hss q hq)
      · rw [if_neg hqp0]; exact hP p ss hss q hq
    · rw [hsent] at hss
      rw [hrecv]
      exact hP p ss hss q hq

/-- **Every reachable `Network`'s views are `Views.Consistent`**, all
    three conjuncts, no further hypothesis. The first holds
    unconditionally (`Network.views_chain_eq`); the second is the
    synchronous-delivery fact (`Nitro.network_views_delivered`); the
    third is `Nitro.network_views_signers`. Every multi-view Liveness
    theorem that took `hv : v.Consistent` alongside `hr` derives it from
    `hr` alone. -/
theorem Nitro.network_views_consistent {apps : Apps E} {Ts : Threats E apps} {n : Network E}
    (h : (Nitro.network apps Ts).Reachable n) : n.views.Consistent :=
  ⟨Network.views_chain_eq n, Nitro.network_views_delivered ⟨_, h⟩, Nitro.network_views_signers h⟩

/-- `base`'s view after receiving every `p₀`-sent state in `sends` that
    names it a recipient, batched as one list (helper for
    `Nitro.participant_reachable_deliver_sends`; a plain `def`, not an
    inline structure update, so it is one unambiguous term throughout). -/
def Nitro.NetworkState.recvBatch {q : Participant} (base : NetworkState E q) (p₀ : Participant)
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
  | nil => (simpa? [NetworkState.recvBatch] using hbase says simpa only [NetworkState.recvBatch, List.filter_nil, List.map_nil, List.nil_append] using hbase)
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
      refine ⟨s₀, hinit, hsteps.tail (Or.inr (Or.inr (Or.inl
        ⟨.deliver ⟨st, [p₀]⟩, (Ts.ok q).toCapable.capableDeliver _ _ hUnforged,
          (fun op h => by cases h), ?_⟩)))⟩
      (simp? [NetworkState.recvBatch, hqr] says simp only [NetworkState.recvBatch, hqr, decide_true, List.filter_cons_of_pos, List.map_cons, List.cons_append, NetworkState.applyAdv_deliver])
    · (simpa? [NetworkState.recvBatch, List.filter_cons, hqr] using ihrest says simpa only [NetworkState.recvBatch, hqr, decide_false, Bool.false_eq_true, not_false_eq_true, List.filter_cons_of_neg] using ihrest)

/-- **Every view of a reachable `Network` is `Nitro.participant`-reachable.**
    The caller rule (design decision 2026-10-29, "Caller rule", read
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
    (n : Nitro.ReachableNetwork apps Ts) (q : Participant) :
    (Nitro.participant apps (Ts.T q)).Reachable (n.state.view q) := by
  obtain_reach ⟨n, h⟩ := n
  refine Machine.invariant (Nitro.network apps Ts)
    (P := fun n => (Nitro.participant apps (Ts.T q)).Reachable (n.view q)) ?_ ?_ n h
  · intro n hinit
    obtain ⟨hc, hs, hrv⟩ := hinit
    refine ⟨_, ?_, Relation.ReflTransGen.refl⟩
    (simp? [Network.view, Nitro.participant, Nitro.participantWith, hc, hs, hrv] says simp only [participant, participantWith, ne_eq, Network.view, hc, hrv, hs])
  · intro n n' hP hstep
    obtain ⟨p₀, ⟨m, hfeas, hvgate, rfl⟩ | ⟨op, hfeas, hsgate, rfl⟩ |
        ⟨m, hfeas, -, hnochain, hnoland, rfl⟩ | ⟨c, e, x, hxle, rfl⟩⟩ :=
      hstep
    · by_cases hqp0 : q = p₀
      · subst hqp0
        have heq : (Network.applyHonest n q m).view q = (n.view q).applyHonest m := by
          cases m with
          | react rr =>
            (simp? [Network.view, Network.applyHonest_react_sent, Network.applyHonest_react_received_self,
              NetworkState.applyHonest] says simp only [Network.view, Network.applyHonest_react_chain, Network.applyHonest_react_received_self, Network.applyHonest_react_sent, ↓reduceIte, NetworkState.applyHonest])
          | wait dt => (simp? [Network.applyHonest, Network.view, NetworkState.applyHonest] says simp only [Network.view, Network.applyHonest, NetworkState.applyHonest])
        rw [heq]
        exact hP.tail (Or.inl ⟨m, hfeas, rfl⟩)
      · cases m with
        | react rr =>
          have heq : (Network.applyHonest n p₀ (.react rr)).view q =
              (n.view q).recvBatch p₀ rr.sends := by
            (simp? [Network.view, Network.applyHonest_react_sent, hqp0,
              Network.applyHonest_react_received, NetworkState.recvBatch] says simp only [Network.view, Network.applyHonest_react_chain, Network.applyHonest_react_received, Network.applyHonest_react_sent, hqp0, ↓reduceIte, NetworkState.recvBatch])
          rw [heq]
          refine Nitro.participant_reachable_deliver_sends hqp0 rr.sends ?_ hP
          intro st hst v hv hqv
          exact hvgate rr rfl st hst v hv q hqv
        | wait dt =>
          have heq : (Network.applyHonest n p₀ (.wait dt)).view q =
              (n.view q).applyAdv apps (.tick dt) := by
            (simp? [Network.applyHonest, Network.view, NetworkState.applyAdv_tick apps] says simp only [Network.view, Network.applyHonest, NetworkState.applyAdv_tick apps])
          rw [heq]
          exact hP.tail (Or.inr (Or.inr (Or.inl ⟨.tick dt, (Ts.ok q).toCapable.capableTick _ dt,
            (fun op h => by cases h), rfl⟩)))
    · by_cases hqp0 : q = p₀
      · subst hqp0
        have heq : (Network.land apps n q op).view q = (n.view q).applyAdv apps (.land op) := by
          cases happly : n.chain.apply apps q op with
          | none => simp only [Network.land, happly, NetworkState.applyAdv_land_none (net := n.view q) apps happly]
          | some s' =>
            simp only [Network.land, happly, NetworkState.applyAdv_land_some (net := n.view q) apps happly]
            (simp? [Network.view] says simp only [Network.view])
        rw [heq]
        exact hP.tail (Or.inr (Or.inl ⟨op, hfeas, rfl⟩))
      · have heq : (Network.land apps n p₀ op).view q =
            (n.view q).applyAdv apps (.chain p₀ op) := by
          cases happly : n.chain.apply apps p₀ op with
          | none =>
            simp only [Network.land, happly, NetworkState.applyAdv_chain_none (net := n.view q) apps happly]
          | some s' =>
            simp only [Network.land, happly, NetworkState.applyAdv_chain_some (net := n.view q) apps happly]
            (simp? [Network.view, if_neg hqp0] says simp only [Network.view])
        rw [heq]
        have hUnforged : ∀ ss ∈ op.proofStates, (n.view q).Unforged ss := by
          intro ss hss
          obtain ⟨hsg, hvoucher⟩ := hsgate ss hss
          exact ⟨fun hqsg => hsg q hqsg, fun v hv hqv => hvoucher v hv q hqv⟩
        have hcap : (Ts.T q).feasible (n.view q) (.chain p₀ op) :=
          (Ts.ok q).toCapable.capable (n.view q) p₀ op (Ne.symm hqp0) hUnforged
        exact hP.tail (Or.inr (Or.inr (Or.inl ⟨.chain p₀ op, hcap, (fun op' h => by cases h),
          rfl⟩)))
    · by_cases hqp0 : q = p₀
      · subst hqp0
        have heq : (Network.applyAdv apps n q m).view q = (n.view q).applyAdv apps m := by
          cases m with
          | chain caller op => exact absurd rfl (hnochain caller op)
          | deliver ss => (simp? [Network.applyAdv_deliver, Network.view] says simp only [Network.view, Network.applyAdv_deliver, ↓reduceIte, NetworkState.applyAdv_deliver])
          | tick dt => (simp? [NetworkState.applyAdv_tick apps, Network.view] says simp only [Network.view, Network.applyAdv_tick, NetworkState.applyAdv_tick apps])
          | land op => exact absurd rfl (hnoland op)
        rw [heq]
        exact hP.tail (Or.inr (Or.inr (Or.inl ⟨m, hfeas, hnoland, rfl⟩)))
      · cases m with
        | chain caller op => exact absurd rfl (hnochain caller op)
        | deliver ss =>
          have heq : (Network.applyAdv apps n p₀ (.deliver ss)).view q = n.view q := by
            (simp? [Network.applyAdv_deliver, Network.view, hqp0] says simp only [Network.view, Network.applyAdv_deliver, hqp0, ↓reduceIte])
          rw [heq]
          exact hP
        | tick dt =>
          have heq : (Network.applyAdv apps n p₀ (.tick dt)).view q =
              (n.view q).applyAdv apps (.tick dt) := by
            (simp? [Network.applyAdv_tick, Network.view, NetworkState.applyAdv_tick apps] says simp only [Network.view, Network.applyAdv_tick, NetworkState.applyAdv_tick apps])
          rw [heq]
          exact hP.tail (Or.inr (Or.inr (Or.inl ⟨.tick dt, (Ts.ok q).toCapable.capableTick _ dt,
            (fun op h => by cases h), rfl⟩)))
        | land op => exact absurd rfl (hnoland op)
    · by_cases hqp0 : q = p₀
      · subst hqp0
        have heq : (Network.deposit n q (.channel c) e x).view q =
            (n.view q).applyAdv apps (.land (.deposit (.channel c) e x)) := by
          cases happly : n.chain.deposit (.channel c) e x with
          | none =>
            simp only [Network.deposit, happly, Adjudicator.apply, NetworkState.applyAdv_land_none (net := n.view q) (op := Op.deposit (.channel c) e x) apps happly]
          | some s' =>
            simp only [Network.deposit, happly, Adjudicator.apply, NetworkState.applyAdv_land_some (net := n.view q) (op := Op.deposit (.channel c) e x) apps happly]
            (simp? [Network.view, Op.proofStates] says simp only [Network.view, Op.proofStates, List.nil_append])
        rw [heq]
        exact hP.tail (Or.inr (Or.inr (Or.inr ⟨.channel c, e, x, rfl⟩)))
      · have heq : (Network.deposit n p₀ (.channel c) e x).view q =
            (n.view q).applyAdv apps (.chain p₀ (.deposit (.channel c) e x)) := by
          cases happly : n.chain.deposit (.channel c) e x with
          | none =>
            simp only [Network.deposit, happly, Adjudicator.apply, NetworkState.applyAdv_chain_none (net := n.view q) (caller := p₀) (op := Op.deposit (.channel c) e x) apps happly]
          | some s' =>
            simp only [Network.deposit, happly, Adjudicator.apply, NetworkState.applyAdv_chain_some (net := n.view q) (caller := p₀) (op := Op.deposit (.channel c) e x) apps happly]
            (simp? [Network.view, Op.proofStates] says simp only [Network.view, Op.proofStates, List.nil_append])
        rw [heq]
        have hUnforged : ∀ ss ∈ (Op.deposit (.channel c) e x : Op E).proofStates,
            (n.view q).Unforged ss := by
          intro ss hss
          (simp? [Op.proofStates] at hss says simp only [Op.proofStates, List.not_mem_nil] at hss)
        have hcap : (Ts.T q).feasible (n.view q) (.chain p₀ (.deposit (.channel c) e x)) :=
          (Ts.ok q).toCapable.capable (n.view q) p₀ (.deposit (.channel c) e x) (Ne.symm hqp0)
            hUnforged
        exact hP.tail (Or.inr (Or.inr (Or.inl ⟨.chain p₀ (.deposit (.channel c) e x), hcap,
          (fun op h => by cases h), rfl⟩)))

/-- **Wallet conservation (D10 design decision).** No coin is created: the chain's
    `held` plus every coin it ever paid to an external destination is
    exactly the sum of every successful deposit along the history
    (`deposits`, an existential witness built by the same induction as
    `Nitro.network_chain_reachableSigned`'s `signed`), and each
    participant's wallet only ever falls by its own deposits — `n0`'s
    wallet at `p` is the sum of what `p` deposited plus what is left in
    `n`'s wallet at `p`. `Participant` is infinite (`Address.lean`, a bare
    `Nat` wrapper), so no sum "over every wallet" type-checks; `deposits`,
    a finite list (any derivation of `Relation.ReflTransGen` is finite),
    is the exact finite record the design decision's "initial total wallets" reads
    against. -/
theorem Nitro.network_conservation {apps : Apps E} {Ts : Threats E apps} {n0 n : Network E}
    (hinit : (Nitro.network apps Ts).init n0)
    (hsteps : Relation.ReflTransGen (Nitro.network apps Ts).step n0 n) :
    ∃ deposits : List (Participant × Coins),
      n.chain.held + n.chain.balances.paidOutTotal = (deposits.map Prod.snd).sum ∧
      ∀ p, n0.wallet p =
        n.wallet p + ((deposits.filter (fun d => decide (d.1 = p))).map Prod.snd).sum := by
  induction hsteps with
  | refl =>
    obtain ⟨hc0, -, -⟩ := hinit
    exact ⟨[], by rw [hc0]; rfl,
      by intro p; simp only [List.filter_nil, List.map_nil, List.sum_nil, add_zero]⟩
  | @tail n1 n2 hs1 hstep ih =>
    obtain ⟨deposits, hheld, hwallet⟩ := ih
    have hr1 : (Nitro.network apps Ts).Reachable n1 := ⟨n0, hinit, hs1⟩
    obtain ⟨p₀, hframe⟩ := Nitro.network.step_frame hstep
    rcases hframe with
        ⟨r, -, hchain, -, -, hwal⟩ | ⟨dt, hchain, -, -, hwal⟩ | hunchanged |
        ⟨op, s', hopfeas, hop, -, hchain, -, -, hwal⟩ | ⟨ss, -, hchain, -, -, hwal⟩ |
        ⟨c, e, x, s', hxle, hdep, hchain, -, -, hwal⟩
    · exact ⟨deposits, by rw [hchain]; exact hheld, by rw [hwal]; exact hwallet⟩
    · exact ⟨deposits, by rw [hchain]; simpa only [Adjudicator.tick] using hheld,
        by rw [hwal]; exact hwallet⟩
    · subst hunchanged
      exact ⟨deposits, hheld, hwallet⟩
    · have hnodep : ∀ a e x, op ≠ Op.deposit a e x := by
        intro a e x heq
        rw [heq] at hopfeas
        simp only [Op.HonestFeasible] at hopfeas
      have hstep' := Adjudicator.held_paidOut_step_no_deposit
        (Nitro.network_chain_reachable hr1) hnodep hop
      exact ⟨deposits, by rw [hchain, hstep']; exact hheld, by rw [hwal]; exact hwallet⟩
    · exact ⟨deposits, by rw [hchain]; exact hheld, by rw [hwal]; exact hwallet⟩
    · have hopEq : n1.chain.apply apps p₀ (.deposit (.channel c) e x) = some s' := hdep
      have hstep' := Adjudicator.held_paidOut_step_deposit (Nitro.network_chain_reachable hr1) hopEq
      refine ⟨(p₀, x) :: deposits, ?_, ?_⟩
      · rw [hchain]
        simp only [List.map_cons, List.sum_cons]
        rw [hstep', hheld, Nat.add_comm]
      · intro q
        rw [hwal]
        by_cases hqp : q = p₀
        · subst hqp
          rw [hwallet q]
          simp only [↓reduceIte, decide_true, List.filter_cons_of_pos, List.map_cons, List.sum_cons]
          rw [← Nat.add_assoc, Nat.sub_add_cancel hxle]
        · have hw := hwallet q
          simp only [hqp, ↓reduceIte, Ne.symm hqp, decide_false, Bool.false_eq_true,
            not_false_eq_true, List.filter_cons_of_neg]
          exact hw

/-- **D10 fix: a reachable network can hold a positive balance in a ledger
    channel.** One deposit from genesis closes the gap the earlier model found
    (named `network_balances_zero` in review notes,
    "D10"): a `Nitro.network`-reachable chain is no longer always
    zero-balance everywhere. -/
theorem Nitro.network_positive_balance_reachable {apps : Apps E} (Ts : Threats E apps)
    (p : Participant) (c : FixedPart) (hck : c.kind = .ledger) (x : Coins) (hx : 0 < x) :
    ∃ n : Network E, (Nitro.network apps Ts).Reachable n ∧
      0 < n.chain.balances.get (.channel c) := by
  set n0 : Network E :=
    { chain := Adjudicator.genesis, sent := fun _ => [], received := fun _ => [],
      wallet := fun q => if q = p then x else 0 } with hn0def
  have hinit : (Nitro.network apps Ts).init n0 := ⟨rfl, rfl, rfl⟩
  have hr0 : (Nitro.network apps Ts).Reachable n0 := ⟨n0, hinit, Relation.ReflTransGen.refl⟩
  have hwle : x ≤ n0.wallet p := by (simp? [hn0def] says simp only [hn0def, ↓reduceIte, Std.le_refl])
  have hstep : (Nitro.network apps Ts).step n0 (Network.deposit n0 p (.channel c) 0 x) :=
    ⟨p, Or.inr (Or.inr (Or.inr ⟨c, 0, x, hwle, rfl⟩))⟩
  refine ⟨Network.deposit n0 p (.channel c) 0 x, hr0.tail hstep, ?_⟩
  have hbal : (Network.deposit n0 p (.channel c) 0 x).chain.balances.get (.channel c) = x := by
    (simp? [Network.deposit, Adjudicator.deposit, hck, hn0def, Adjudicator.genesis,
      Balances.add, Balances.set, Balances.get] says simp only [Balances.get, Network.deposit, Adjudicator.deposit, hck, hn0def, Adjudicator.genesis, List.lookup_nil, Option.getD_none, and_self, ↓reduceIte, Balances.add, Balances.set, zero_add, ne_eq, decide_not, List.filter_nil, Nat.sub_self, List.lookup_cons_self, Option.getD_some])
  rw [hbal]; exact hx

end ArmadaLean
