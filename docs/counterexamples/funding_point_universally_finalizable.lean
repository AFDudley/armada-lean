/-
  Counterexample to `funding_point_universally_finalizable` (Liveness.lean),
  Nitro-23 (Nitro:635-636), pebble `aln-cc8`, defect D11
  (`docs/nitro-repair-2026-10-27.md` section 7).

  The model lets an honest participant sign two different states at one
  turn number. `Nitro.network` gates an honest send only by
  `Network.VoucherSendable`. `AtFundingPoint` bounds the turn number of a
  sent state, not its outcome.

  The network `nE` starts at genesis and has three honest sends on the
  two-participant channel `c2 = [p0, q0]` (`c2.n = 2`):
  * `p0` sends `sA0` (turn 0, outcome `Ωg`).
  * `q0` sends `sA1` (turn 1, outcome `Ωg`).
  * `q0` also sends `sB1` (turn 1, outcome `Ωb ≠ Ωg`).
  Each recipient gets each send (`State.recipients`). So every participant
  holds the turn-0 and turn-1 states with outcome `Ωg`: `AtFundingPoint`
  holds for `Ωg`. Every other hypothesis holds, with `vtAll` (the game
  library that keeps the outcome) and the canonical threats `Ts apps1`.

  `q0` is the mover of turn 1, the last turn below `c2.n`. In `q0`'s game,
  `p0` is the adversary. Before `q0`'s first call lands, the adversary
  challenges `c2` with the proof `[sB1 by q0, sB2 by p0]`. `sB2` is
  turn 2 with outcome `Ωb`, signed by `p0`. The record is then 2. Every
  proof that `q0` can submit for an `Ωg` candidate needs a `p0` signature
  at an even turn. The only `p0` signatures that `q0` holds are on `sA0`
  (turn 0) and `sB2` (turn 2, `Ωb`). So an `Ωg` candidate has turn at
  most 1 (`cand_low`), below the record. No call of `q0` can register an
  `Ωg` candidate, and the adversary never signs one. `Ωg` never finalizes
  (`not_finalizable`), and `funding_point_universally_finalizable_false`
  refutes the theorem.

  ForceMove:783-784 (section 3.1.5, "Alternative moves"): "Nothing in the
  conditions prevents a player from signing multiple valid moves with the
  same turnNum." ForceMove:793-794: "In providing alternative moves, the
  player gives the next player the right to choose the move they want to
  progress from." Here the next player is the adversary `p0`.

  The participant that equivocates must be the last mover below `c.n`.
  If `p0` equivocates at turn 0 instead, `p0` can answer at turn 2: `p0`
  holds `q0`'s turn-1 state with outcome `Ωg` [INFERENCE, not checked].

  go-nitro does not sign two different states at one turn number:
  `Channel.SignAndAddState` (channel/channel.go:343-358) returns an error
  when `AddSignedState` (channel.go:315-321) fails, and
  `SignedState.Merge` (channel/state/signedstate.go:93-95) fails on a
  different state. `docs/nitro-repair-2026-10-27.md` section 7 gives the
  proposed repair.

  This file is not part of the `ArmadaLean` library. Check it with
  `lake env lean docs/counterexamples/funding_point_universally_finalizable.lean`.
  `funding_point_universally_finalizable_false` uses only `propext`,
  `Classical.choice` and `Quot.sound`.
-/
import ArmadaLean.Nitro.NonVacuity

namespace ArmadaLean.Nitro.Counterexample.FundingPoint

open ArmadaLean.Nitro ArmadaLean.Nitro.NonVacuity

/-- `omega` after unfolding the `Time` abbreviation. -/
macro "tomega" : tactic => `(tactic| ((try unfold Time at *); omega))

/-! ## The states and the network -/

def o2 : Allocation Nat := [alloc d1 1]
/-- The outcome every participant holds at the funding point. -/
def Ωg : Outcome Nat := .allocation o1
/-- The outcome of `q0`'s second turn-1 state. -/
def Ωb : Outcome Nat := .allocation o2

theorem Ωb_ne_Ωg : Ωb ≠ Ωg := by decide

def sA0 : State Nat := ⟨c2, 0, Ωg, false, .opaque 0⟩
def sA1 : State Nat := ⟨c2, 1, Ωg, false, .opaque 0⟩
def sB1 : State Nat := ⟨c2, 1, Ωb, false, .opaque 0⟩
/-- The adversary's turn-2 state, signed for `p0`. -/
def sB2 : State Nat := ⟨c2, 2, Ωb, false, .opaque 0⟩

def n0 : Network Nat := ⟨g0, fun _ => [], fun _ => [], noDeposits⟩
def nA : Network Nat := n0.applyHonest p0 (.send sA0)
def nB : Network Nat := nA.applyHonest q0 (.send sA1)
/-- `q0` sends a second, different turn-1 state. -/
def nE : Network Nat := nB.applyHonest q0 (.send sB1)

theorem voucher_gate (n : Network Nat) (st : State Nat) (hst : st.voucher? = none) :
    ∀ r : Reaction Nat, HonestMove.send st = .react r → ∀ st' ∈ r.sends, n.VoucherSendable st' := by
  intro r hr st' hst'
  injection hr with hr; subst hr
  simp only [List.mem_singleton] at hst'; subst hst'
  intro v hv; rw [hst] at hv; cases hv

theorem nE_reach : (Nitro.network apps1 (Ts apps1)).Reachable nE :=
  network_reachable_honest
    (network_reachable_honest
      (network_reachable_honest (network_reachable_init apps1 (Ts apps1) noDeposits) p0 (.send sA0)
        (by simp) (voucher_gate _ _ rfl))
      q0 (.send sA1) (by simp) (voucher_gate _ _ rfl))
    q0 (.send sB1) (by simp) (voucher_gate _ _ rfl)

theorem nE_views_p0 : nE.views p0 = ⟨g0, [⟨sB1, [q0]⟩, ⟨sA1, [q0]⟩], [⟨sA0, [p0]⟩]⟩ := by
  simp [nE, nB, nA, n0, Network.views, Network.view, Network.applyHonest, HonestMove.send,
    State.recipients, sA0, sA1, sB1, c2, p0, q0]

theorem nE_views_q0 : nE.views q0 = ⟨g0, [⟨sA0, [p0]⟩], [⟨sB1, [q0]⟩, ⟨sA1, [q0]⟩]⟩ := by
  simp [nE, nB, nA, n0, Network.views, Network.view, Network.applyHonest, HonestMove.send,
    State.recipients, sA0, sA1, sB1, c2, p0, q0]

theorem nE_views_chain (r : Participant) : (nE.views r).chain = g0 := rfl

/-! ## Every hypothesis of the theorem holds -/

theorem atFundingPoint : AtFundingPoint nE.views c2 Ωg := by
  refine ⟨?_, ?_⟩
  · intro r hr k hk
    have hr' : r = p0 ∨ r = q0 := by simpa [c2] using hr
    have hk' : k = 0 ∨ k = 1 := by
      have : k < 2 := by simpa [FixedPart.n, c2] using hk
      omega
    rcases hk' with rfl | rfl
    · refine ⟨⟨sA0, [p0]⟩, ?_, rfl, rfl, rfl, rfl, ⟨p0, by decide, by decide⟩⟩
      rcases hr' with rfl | rfl
      · rw [nE_views_p0]; exact holds_intro _ _ (by decide) (fun _ h => by cases h)
      · rw [nE_views_q0]; exact holds_intro _ _ (by decide) (fun _ h => by cases h)
    · refine ⟨⟨sA1, [q0]⟩, ?_, rfl, rfl, rfl, rfl, ⟨q0, by decide, by decide⟩⟩
      rcases hr' with rfl | rfl
      · rw [nE_views_p0]; exact holds_intro _ _ (by decide) (fun _ h => by cases h)
      · rw [nE_views_q0]; exact holds_intro _ _ (by decide) (fun _ h => by cases h)
  · intro r hr ss hss _
    have hr' : r = p0 ∨ r = q0 := by simpa [c2] using hr
    rcases hr' with rfl | rfl
    · rw [nE_views_p0] at hss
      simp only [List.mem_singleton] at hss; subst hss; decide
    · rw [nE_views_q0] at hss
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hss
      rcases hss with rfl | rfl <;> decide

/-! ## The invariant of `q0`'s game -/

/-- What a `p0` signature on a state of `c2` can carry: the state is not
    final, and from turn 2 on it is `sB2`'s turn and outcome. -/
def Good (st : State Nat) : Prop :=
  st.isFinal = false ∧ (2 ≤ st.turnNum → st.turnNum = 2 ∧ st.outcome = Ωb)

/-- A signed state whose `p0` signature on `c2` is `Good`. -/
def GoodP0 (ss : SignedState Nat) : Prop :=
  p0 ∈ ss.signers → ss.state.channel = c2 → Good ss.state

/-- Every `p0` signature that `q0` received is `Good`. -/
def PSig (n : NetworkState Nat q0) : Prop := ∀ r ∈ n.received, GoodP0 r

/-- A status of `c2` from which `Ωg` never finalizes: the record is at
    least 2 and a challenge or a finalization does not carry `Ωg`. -/
def Safe : ChannelStatus Nat → Prop
  | .open t => 2 ≤ t
  | .challenged t ch => 2 ≤ t ∧ ch.state.outcome ≠ Ωg
  | .finalized _ f _ => f ≠ Ωg

def Inv (n : NetworkState Nat q0) : Prop := PSig n ∧ Safe (n.chain.statusOf c2)
variable {E : Type} [DecidableEq E]

/-- Every element of a `forceMoveRules` support proof is a state of `c`:
    unfolds `forceMoveRules.supports`'s own `proof.all (channel = c)`
    conjunct, dropped by `forceMove_supports_valid_run`. -/
theorem forceMove_supports_all_channel {vt : State E → State E → Bool} {c : FixedPart}
    {proof : SupportProof E} {candidate : State E}
    (h : (forceMoveRules vt).supports c proof candidate = true) :
    ∀ m ∈ proof, m.state.channel = c := by
  simp only [forceMoveRules, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨-, -⟩, -⟩, hall⟩, -⟩ := h
  intro m hm
  exact of_decide_eq_true (List.all_eq_true.mp hall m hm)

/-- `forceMoveRules.supports`'s own `proof.head?.all byMover` conjunct,
    dropped by `forceMove_supports_valid_run`: the first state of the proof
    is signed by its mover, same as every later one
    (`forceMove_supports_valid_run`'s middle conjunct gives it for position
    `i + 1`, never for position `0`). -/
theorem forceMove_supports_head_byMover {vt : State E → State E → Bool} {c : FixedPart}
    {proof : SupportProof E} {candidate : State E}
    (h : (forceMoveRules vt).supports c proof candidate = true)
    {m0 : SignedState E} (h0 : proof[0]? = some m0) : m0.ByMover := by
  simp only [forceMoveRules, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨-, hhead⟩, -⟩, -⟩, -⟩ := h
  have hm0 : proof.head? = some m0 := by
    cases proof with
    | nil => simp at h0
    | cons a t => simpa using h0
  rw [hm0] at hhead
  exact (SignedState.byMover_iff m0).1 hhead

omit [DecidableEq E] in
/-- `ByMover`'s witness mover is the state's own `mover`, uniquely: once
    `s.mover = some p` is known, `ByMover` forces `p` itself (not merely
    some signer) into the signer list. -/
theorem _root_.ArmadaLean.Nitro.SignedState.ByMover.signer_of_mover {ss : SignedState E} (hbm : ss.ByMover)
    {p : Participant} (hmv : ss.state.mover = some p) : p ∈ ss.signers := by
  obtain ⟨m, hm, hms⟩ := hbm
  rw [hmv] at hm
  cases hm
  exact hms

theorem p0_ne_q0 : p0 ≠ q0 := by decide

theorem goodP0_of_holds {n : NetworkState Nat q0} (hps : PSig n) {ss : SignedState Nat}
    (hh : n.Holds ss) : GoodP0 ss := by
  intro hp hc
  rcases hh.1 p0 hp with ⟨h, -⟩ | ⟨r, hr, hrs, hpr⟩
  · exact absurd h p0_ne_q0
  · rw [← hrs]; exact hps r hr hpr (by rw [hrs]; exact hc)

theorem p0_signs_even {ss : SignedState Nat} (hbm : ss.ByMover) (hc : ss.state.channel = c2)
    (he : ss.state.turnNum % 2 = 0) : p0 ∈ ss.signers :=
  hbm.signer_of_mover (by
    have h2 : c2.n = 2 := rfl
    simp only [State.mover, hc, h2, he]; rfl)

/-- The key fact: every `forceMoveRules vtAll` candidate with outcome `Ωg`
    whose `p0` signatures are `Good` has turn number at most 1. -/
theorem cand_low {proof : SupportProof Nat} {cand : State Nat}
    (h : (forceMoveRules vtAll).supports c2 proof cand = true) (hg : ∀ ss ∈ proof, GoodP0 ss)
    (hΩ : cand.outcome = Ωg) : cand.turnNum ≤ 1 := by
  obtain ⟨hlen, hstep, mlast, hlast, hmc⟩ := forceMove_supports_valid_run vtAll c2 proof cand h
  have hall := forceMove_supports_all_channel h
  have hhead := @forceMove_supports_head_byMover _ _ _ _ _ _ h
  have hkeep := forceMove_conclude_keeps_outcome vtAll c2 proof cand h
  have hlen2 : proof.length = 2 := hlen
  rcases proof with _ | ⟨m1, _ | ⟨m2, _ | ⟨m3, rest⟩⟩⟩
  · simp at hlen2
  · simp at hlen2
  · simp only [List.getLast?_cons_cons, List.getLast?_singleton, Option.some.injEq] at hlast
    subst hlast; subst hmc
    obtain ⟨-, hturn, hbm2, hvt⟩ := hstep 0 m1 m2 rfl rfl
    have hbm1 : m1.ByMover := hhead rfl
    have hout : m2.state.outcome = m1.state.outcome := by
      cases hf : m2.state.isFinal
      · simpa [vtAll] using hvt hf
      · exact (hkeep 0 m1 m2 rfl rfl).1 hf
    have hc1 : m1.state.channel = c2 := hall m1 (by simp)
    have hc2 : m2.state.channel = c2 := hall m2 (by simp)
    have hg1 := hg m1 (by simp)
    have hg2 := hg m2 (by simp)
    rcases Nat.mod_two_eq_zero_or_one m1.state.turnNum with he | ho
    · have hG := hg1 (p0_signs_even hbm1 hc1 he) hc1
      by_cases h2 : 2 ≤ m1.state.turnNum
      · exact absurd (hΩ.symm.trans (hout.trans (hG.2 h2).2)) (Ne.symm Ωb_ne_Ωg)
      · omega
    · have he2 : m2.state.turnNum % 2 = 0 := by omega
      have hG := hg2 (p0_signs_even hbm2 hc2 he2) hc2
      exact absurd (hΩ.symm.trans (hG.2 (by omega)).2) (Ne.symm Ωb_ne_Ωg)
  · simp at hlen2

/-- No conclusion proof for `c2` has `Good` `p0` signatures. -/
theorem no_conclusion {ss : SignedState Nat} (hg : GoodP0 ss) : ¬ ConclusionProof c2 ss := by
  rintro ⟨hc, hfin, hall⟩
  have hp : p0 ∈ ss.signers := hall p0 (by rw [hc]; simp [c2])
  have := (hg hp hc).1
  rw [hfin] at this; cases this

theorem safe_record {st : ChannelStatus Nat} {now : Time} (hs : Safe st)
    (hm : st.mode now ≠ .finalized) : 2 ≤ st.turnNumRecord := by
  cases st with
  | «open» t => exact hs
  | challenged t ch => exact hs.1
  | finalized t f o => exact absurd rfl hm

theorem safe_withOutcome {st : ChannelStatus Nat} {now : Time} {x o : Outcome Nat} (hs : Safe st)
    (hf : st.finalOutcome now = some x) : Safe (st.withOutcome o) := by
  cases st with
  | «open» t => simp at hf
  | challenged t ch => exact hs.2
  | finalized t f o' => exact hs

theorem safe_not_finalized {st : ChannelStatus Nat} {now : Time} (hs : Safe st) :
    st.finalizedWith now ≠ some Ωg := by
  cases st with
  | «open» t => simp
  | challenged t ch =>
    simp only [ChannelStatus.finalizedWith]
    split
    · intro h; exact hs.2 (Option.some.inj h)
    · simp
  | finalized t f o => intro h; exact hs (Option.some.inj h)

/-- One successful operation whose `p0` signatures are `Good` keeps `c2` safe. -/
theorem safe_step {caller : Participant} {op : Op Nat} {s s' : Adjudicator Nat}
    (h : s.apply apps1 caller op = some s') (hg : ∀ ss ∈ op.proofStates, GoodP0 ss)
    (hs : Safe (s.statusOf c2)) : Safe (s'.statusOf c2) := by
  by_cases ht : Op.targets op c2
  · cases op with
    | deposit a e x => simp [Op.targets] at ht
    | tick dt => simp [Op.targets] at ht
    | transfer a b =>
      simp only [Op.targets] at ht; subst ht
      obtain ⟨o, amt, x, hf, -, -, -, -, hst, -⟩ := Adjudicator.transfer_some h
      rw [Adjudicator.statusOf_of_status hst]
      simp only [Adjudicator.statusOf_setStatus]
      simp only [FixedPart.address_eq, Adjudicator.finalOutcome_channel] at hf
      exact safe_withOutcome hs hf
    | reclaim l v =>
      simp only [Op.targets] at ht; subst ht
      obtain ⟨oL, -, -, -, -, hL, -, -, -, -, -, rfl, -, -⟩ := Adjudicator.reclaim_some h
      simp only [Adjudicator.statusOf_setStatus]
      simp only [FixedPart.address_eq, Adjudicator.finalOutcome_channel] at hL
      exact safe_withOutcome hs hL
    | challenge c' proof cand =>
      simp only [Op.targets] at ht; subst ht
      obtain ⟨⟨-, hsup, -, hmode⟩, rfl⟩ := Adjudicator.challenge_some h
      have hrec : 2 ≤ (s.statusOf c2).turnNumRecord := by
        refine safe_record (now := s.now) hs ?_
        rw [← Adjudicator.mode_eq]
        rcases hmode with ⟨hm, -⟩ | ⟨hm, -⟩ <;> rw [hm] <;> decide
      have hturn : 2 ≤ cand.turnNum := by
        rcases hmode with ⟨-, hle⟩ | ⟨-, hlt⟩ <;> tomega
      simp only [Adjudicator.statusOf_setStatus]
      refine ⟨hturn, fun hΩ => ?_⟩
      have := cand_low hsup hg hΩ
      omega
    | checkpoint c' proof cand =>
      simp only [Op.targets] at ht; subst ht
      obtain ⟨⟨hopen, -, -, hlt⟩, rfl⟩ := Adjudicator.checkpoint_some h
      have hrec : 2 ≤ (s.statusOf c2).turnNumRecord := safe_record hs hopen
      simp only [Adjudicator.statusOf_setStatus]
      show 2 ≤ cand.turnNum
      omega
    | conclude c' ss =>
      simp only [Op.targets] at ht; subst ht
      obtain ⟨⟨-, hcp⟩, -⟩ := Adjudicator.conclude_some h
      exact absurd hcp (no_conclusion (hg ss (by simp [Op.proofStates])))
  · rw [statusOf_apply_of_not_targets h ht]; exact hs

/-! ## The adversary's play -/

/-- `q0`'s adversary: the canonical threat of `NonVacuity.lean`. -/
abbrev T : Threat Nat q0 := (Ts apps1).T q0

/-- Landing one call of `q0` keeps the invariant and the clock. -/
theorem land_inv (n : NetworkState Nat q0) (hI : Inv n) (op : Op Nat) (hop : ∀ dt, op ≠ .tick dt)
    (hg : ∀ ss ∈ op.proofStates, GoodP0 ss) :
    Inv (n.applyAdv apps1 (.land op)) ∧ (n.applyAdv apps1 (.land op)).chain.now = n.chain.now := by
  simp only [NetworkState.applyAdv]
  cases happ : n.chain.apply apps1 q0 op with
  | none => exact ⟨hI, rfl⟩
  | some s' =>
    refine ⟨⟨?_, safe_step happ hg hI.2⟩, Adjudicator.apply_now_eq_of_not_tick hop happ⟩
    intro r hr
    rcases List.mem_append.1 hr with hr | hr
    · exact hg r hr
    · exact hI.1 r hr

/-- `q0`'s calls land one after the other, the clock does not move, and the
    invariant holds. -/
theorem land_all (t : Time) : ∀ (pending : List (Op Nat)),
    (∀ op ∈ pending, (∀ dt, op ≠ .tick dt) ∧ ∀ ss ∈ op.proofStates, GoodP0 ss) →
    ∀ (n : NetworkState Nat q0), Inv n →
      ∃ n', Threat.RoundSeq apps1 T t pending n n' ∧ Inv n' ∧ n'.chain.now = n.chain.now := by
  intro pending
  induction pending with
  | nil => intro _ n hI; exact ⟨n, .nil, hI, rfl⟩
  | cons op rest ih =>
    intro hgood n hI
    obtain ⟨hop, hps⟩ := hgood op List.mem_cons_self
    obtain ⟨hI1, hnow1⟩ := land_inv n hI op hop hps
    obtain ⟨n', hseq, hI', hnow'⟩ :=
      ih (fun op' h => hgood op' (List.mem_cons_of_mem op h)) _ hI1
    exact ⟨n', .land (l1 := []) (l2 := rest) rfl hseq, hI', by rw [hnow', hnow1]⟩

/-- Every call of a feasible move of `q0` is not a tick and carries only
    `Good` `p0` signatures. -/
theorem calls_good {n : NetworkState Nat q0} (hps : PSig n) {m : HonestMove Nat}
    (hfeas : m.Feasible n) :
    ∀ op ∈ m.calls, (∀ dt, op ≠ .tick dt) ∧ ∀ ss ∈ op.proofStates, GoodP0 ss := by
  cases m with
  | wait dt => intro op hop; simp [HonestMove.calls] at hop
  | react r =>
    intro op hop
    have h := hfeas op hop
    refine ⟨?_, ?_⟩
    · intro dt heq; subst heq; exact h
    · intro ss hss
      cases op with
      | deposit => exact absurd h id
      | tick => exact absurd h id
      | transfer => simp [Op.proofStates] at hss
      | reclaim => simp [Op.proofStates] at hss
      | challenge c proof cand => exact goodP0_of_holds hps (h ss hss)
      | checkpoint c proof cand => exact goodP0_of_holds hps (h ss hss)
      | conclude c ss' => exact goodP0_of_holds hps (h ss hss)

theorem inv_applyHonest {n : NetworkState Nat q0} (hI : Inv n) (m : HonestMove Nat) :
    Inv (n.applyHonest m) := by
  cases m with
  | react r => exact hI
  | wait dt => exact ⟨hI.1, by simpa [NetworkState.applyHonest] using hI.2⟩

/-- From any state with the invariant, the adversary lands `q0`'s calls
    and does nothing else. -/
theorem round_inv (n : NetworkState Nat q0) (hI : Inv n) (m : HonestMove Nat) (hfeas : m.Feasible n) :
    ∃ n', T.Round apps1 m n n' ∧ Inv (n'.applyHonest m) := by
  obtain ⟨n', hseq, hI', hnow⟩ := land_all n.chain.now m.calls (calls_good hI.1 hfeas) n hI
  refine ⟨n', ⟨hseq, ?_⟩, inv_applyHonest hI' m⟩
  rw [hnow]; exact Nat.lt_add_of_pos_right T.ε_pos

theorem not_unbeatable (n : NetworkState Nat q0)
    (h : UnbeatableIn apps1 T (fun _ => True) (fun n => n.Finalized c2 Ωg) n) : Inv n → False := by
  induction h with
  | done hG =>
    intro hI
    simp only [NetworkState.Finalized, FixedPart.address_eq, Adjudicator.finalizedWith_channel] at hG
    exact safe_not_finalized hI.2 hG
  | move m _ hfeas _ ih =>
    intro hI
    obtain ⟨n', hR, hI'⟩ := round_inv _ hI m hfeas
    exact ih n' hR hI'

/-! ## The first round: the adversary challenges with `q0`'s other state -/

def badProof : SupportProof Nat := [⟨sB1, [q0]⟩, ⟨sB2, [p0]⟩]
def badOp : Op Nat := .challenge c2 badProof sB2

def net0 : NetworkState Nat q0 := ⟨g0, [⟨sA0, [p0]⟩], [⟨sB1, [q0]⟩, ⟨sA1, [q0]⟩]⟩

theorem net0_eq : nE.views q0 = net0 := nE_views_q0

def s1 : Adjudicator Nat := g0.setStatus c2 (.challenged 2 ⟨sB2, 0 + c2.challengeDuration⟩)

theorem g0_bad : g0.apply apps1 p0 badOp = some s1 := by
  simp only [badOp, Adjudicator.apply_challenge, Adjudicator.challenge]
  rw [if_pos (by decide)]
  rfl

def net1 : NetworkState Nat q0 := net0.applyAdv apps1 (.chain p0 badOp)

theorem net1_eq : net1 = ⟨s1, badProof ++ [⟨sA0, [p0]⟩], [⟨sB1, [q0]⟩, ⟨sA1, [q0]⟩]⟩ := by
  have h : net0.chain.apply apps1 p0 badOp = some s1 := g0_bad
  show (match net0.chain.apply apps1 p0 badOp with
    | some s' => ({ net0 with chain := s', received := badOp.proofStates ++ net0.received } :
        NetworkState Nat q0)
    | none => net0) = _
  rw [h]; rfl

theorem net1_inv : Inv net1 := by
  rw [net1_eq]
  refine ⟨?_, ?_⟩
  · intro r hr hp hc
    simp only [badProof, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact absurd hp (by decide)
    · exact ⟨rfl, fun _ => ⟨rfl, rfl⟩⟩
    · exact ⟨rfl, fun h => by simp [sA0] at h⟩
  · show Safe (s1.statusOf c2)
    simp only [s1, Adjudicator.statusOf_setStatus]
    exact ⟨le_refl 2, Ωb_ne_Ωg⟩

theorem bad_feasible : T.feasible net0 (.chain p0 badOp) := by
  refine ⟨p0_ne_q0, fun ss hss => ?_⟩
  simp only [badOp, Op.proofStates, badProof, List.mem_cons, List.not_mem_nil, or_false] at hss
  rcases hss with rfl | rfl
  · exact unforged_intro _ _ (fun _ => ⟨⟨sB1, [q0]⟩, by simp [net0], rfl⟩) (fun _ h => by cases h)
  · exact unforged_intro _ _ (fun h => absurd h (by decide)) (fun _ h => by cases h)

/-- The adversary challenges with `badOp`, then lands `q0`'s calls. -/
theorem first_round (m : HonestMove Nat) (hfeas : m.Feasible net0) :
    ∃ n', T.Round apps1 m net0 n' ∧ Inv (n'.applyHonest m) := by
  have hps0 : PSig net0 := by
    intro r hr hp hc
    simp only [net0, List.mem_singleton] at hr; subst hr
    exact ⟨rfl, fun h => by simp [sA0] at h⟩
  obtain ⟨n', hseq, hI', hnow⟩ :=
    land_all net0.chain.now m.calls (calls_good hps0 hfeas) net1 net1_inv
  have hnow1 : net1.chain.now = net0.chain.now := by rw [net1_eq]; rfl
  refine ⟨n', ⟨.other bad_feasible (by intro dt h; cases h) (by intro o h; cases h) hseq, ?_⟩,
    inv_applyHonest hI' m⟩
  rw [hnow, hnow1]; exact Nat.lt_add_of_pos_right T.ε_pos

/-- `Ωg` is not finalizable for `q0` at the funding point. -/
theorem not_finalizable : ¬ Finalizable apps1 T c2 Ωg (nE.views q0) := by
  rw [net0_eq]
  intro h
  unfold Finalizable Unbeatable at h
  generalize hn : net0 = n at h
  cases h with
  | done hG =>
    subst hn
    simp [NetworkState.Finalized, net0, g0, Adjudicator.genesis, Adjudicator.statusOf] at hG
  | move m _ hfeas hall =>
    subst hn
    obtain ⟨n', hR, hI⟩ := first_round m hfeas
    exact not_unbeatable _ (hall n' hR) hI

/-! ## The counterexample -/

/-- Every hypothesis of `funding_point_universally_finalizable` holds for
    `apps1`, `Ts apps1`, `nE`, `c2`, `Ωg` and `vtAll`, and the conclusion
    fails: `Ωg` is not finalizable for `q0`. -/
theorem funding_point_universally_finalizable_false :
    ¬ ∀ (apps : Apps Nat) (Ts : Threats Nat apps) (v : Views Nat) (n : Network Nat)
        (_hr : (Nitro.network apps Ts).Reachable n) (_hvn : v = n.views) (c : FixedPart)
        (Ω : Outcome Nat) (vt : State Nat → State Nat → Bool)
        (_hc : apps c.appDef = forceMoveRules vt) (_hsetup : SetupPhaseKeepsOutcome vt c)
        (_hvt : SetupPhaseAccepted vt c) (_hn : 0 < c.n)
        (_hdur : ∀ p, 2 * (Ts.T p).ε ≤ c.challengeDuration) (_h : AtFundingPoint v c Ω)
        (_hchain : ∀ p, (v p).chain.mode c = .open ∧ (v p).chain.statusOf c = .open 0),
        UniversallyFinalizable apps Ts v c Ω := by
  intro h
  have hU := h apps1 (Ts apps1) nE.views nE nE_reach rfl c2 Ωg vtAll rfl
    (fun s1 s2 h _ _ => by simpa [vtAll] using h)
    (fun s1 s2 _ _ _ _ ho _ => by simp [vtAll, ho])
    (by decide) (fun _ => (by decide : 2 * 1 ≤ 2)) atFundingPoint
    (fun r => by rw [nE_views_chain]; exact ⟨rfl, rfl⟩)
  exact not_finalizable (hU q0 (by simp [c2]))


/-- The canonical own-violation: `q0` signed two setup states at turn 1, so the
    restated theorem makes no promise to `q0`. -/
theorem q0_made_alternative_moves : ¬ MadeNoAlternativeSetupMoves (nE.views q0) c2 := by
  intro h
  have h_eq := h ⟨sB1, [q0]⟩ (by simp [nE_views_q0])
                  ⟨sA1, [q0]⟩ (by simp [nE_views_q0])
                  (by simp [sB1, c2])
                  (by simp [sA1, c2])
                  (by decide)
                  (by decide)
  simp [sB1, sA1, Ωb_ne_Ωg] at h_eq
end ArmadaLean.Nitro.Counterexample.FundingPoint

#print axioms ArmadaLean.Nitro.Counterexample.FundingPoint.funding_point_universally_finalizable_false
