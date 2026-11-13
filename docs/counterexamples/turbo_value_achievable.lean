/-
  Counterexample to the unconstrained `turbo_value_achievable`
  (`ArmadaLean/Nitro/Liveness.lean`).

  `turbo_value_achievable` claimed that whenever `net.chain.TurboValue
  (.external d) v` holds, `p` has an unbeatable transfer-only strategy
  obtaining `v` at `d` (`CanObtainIn apps T HonestMove.IsTransfer (.external
  d) v net`). `TurboValue` (`Value.lean`) computes `v` by walking a
  topological order of `Adjudicator.Edge` and paying each node's allocation
  forward (`payoutValues`); `Edge n d` only requires `d.isExternal = false`,
  so an allocation entry naming a *virtual* channel is an edge just like one
  naming a ledger channel. But a real `Adjudicator.transfer a b`
  (`Adjudicator.lean`) requires `a.kind = .ledger` *and* `b.fundable = true`
  (`Address.fundable`, false for a virtual channel address): a transfer can
  move coins neither out of nor into a virtual channel
  (`Reachable.lean`'s `balances_virtual_zero_step`, `transfer` case, already
  states exactly this fact and is why a virtual channel's balance is an
  invariant zero). `TurboValue`'s abstract redistribution does not respect
  that restriction, so whenever the only path from a funded ledger channel
  to the destination routes through a virtual channel, the abstract value
  is not transfer-achievable.

  The witness: a single-participant ledger channel `myL` (so `p0` alone can
  sign and conclude it, no adversary cooperation needed) deposits 1 coin,
  then concludes allocating its 1 coin entirely to a single-participant
  *virtual* channel `myV`; `myV` concludes allocating its 1 coin entirely to
  the external destination `myD`. The resulting chain is reachable
  (`net5_reach`, five steps: a `Nitro.participant` deposit step, `p0`'s
  sends of `stV` and then `stL`, and two lands), is a DAG (`chain5_dag`, exactly one edge, `myL →
  myV`), and has Turbo value 1 at `myD` along the order `[myL.address,
  myV.address]` (`chain5_turboValue`). But `chain5.transfer a b = none` for
  EVERY `a b` (`chain5_transfer_none`): the only entry anywhere is `myL`'s,
  naming the non-`fundable` `myV.address`, so no transfer call this chain
  ever admits can move a coin. That makes `chain5` a literal fixed point
  under any transfer-only play (`chain5_applyAll_fixed`), so the external
  balance at `myD` — `0` at `net5` — can never rise to `1`, however many
  rounds are played (`not_canObtain`): `CanObtainIn` is a finite inductive
  derivation (`UnbeatableIn`), and no finite derivation reaches a goal that
  is never true along any play. `turbo_value_achievable_false` states this
  as the refutation of the (hypothesis-for-hypothesis identical) universal
  statement.

  Resolved (`docs/lean/typed-library.md` §4,
  row `Outcome.lean`): `turbo_value_achievable` now takes `net.chain` in
  Turbo scope (`Adjudicator.IsTurboOutcomeNetwork`, `ArmadaLean/Types/
  Outcome.lean`), not just `IsDAG`. `chain5` no longer satisfies the new
  premise: `chain5_not_turboScope` shows `myV` is a Turbo-scope *source*
  (it carries the allocation `[entryD]`, `chain5_allocationOf_V`) that is
  not a ledger channel (`myV.kind = .virtual`), so `chain5.TurboScope`
  fails. `chain5_not_turboOutcomeNetwork` draws the same conclusion for the
  combined premise. The old, unconstrained `turbo_value_achievable_false`
  stays below: it documents why the stronger premise was needed, over the
  identical (now-superseded) hypothesis list.

  This file is not part of the `ArmadaLean` library. Check it with
  `lake env lean docs/counterexamples/turbo_value_achievable.lean`.
-/
import ArmadaLean.Nitro.NonVacuity
import ArmadaLean.Types.Outcome

namespace ArmadaLean.Nitro.Counterexample

open ArmadaLean.Nitro
open ArmadaLean.Nitro.NonVacuity

/-- A single-participant ledger channel. -/
def myL : FixedPart := ⟨[p0], 200, ⟨0⟩, 2, .ledger⟩

/-- A single-participant virtual channel. -/
def myV : FixedPart := ⟨[p0], 201, ⟨0⟩, 2, .virtual⟩

/-- The external destination. -/
def myD : Address Nat := .external 0

theorem myL_ne_myV : myL ≠ myV := by decide

theorem channel_inj {c c' : FixedPart} (h : (Address.channel c : Address Nat) = .channel c') :
    c = c' := by injection h

/-- `myL`'s sole allocation entry: everything to `myV`. -/
def entryV : Entry Nat := alloc (.channel myV) 1

/-- `myV`'s sole allocation entry: everything to the external destination. -/
def entryD : Entry Nat := alloc myD 1

def stL : State Nat := ⟨myL, 0, .allocation [entryV], true, .opaque 0⟩
def ssL : SignedState Nat := ⟨stL, [p0]⟩

def stV : State Nat := ⟨myV, 0, .allocation [entryD], true, .opaque 0⟩
def ssV : SignedState Nat := ⟨stV, [p0]⟩

/-! ## Reaching the witness chain, one `Nitro.participant` step at a time. -/

def net0 : NetworkState Nat p0 := ⟨Adjudicator.genesis, [], []⟩

theorem net0_reach : (Nitro.participant apps0 (turboT p0)).Reachable net0 :=
  participant_reachable_init apps0 (turboT p0)

-- Step 1: deposit 1 coin into `myL` (the wallet-free over-approximation
-- step of `Nitro.participant`'s `step`, 4th disjunct).
def chain1 : Adjudicator Nat := { balances := [(.channel myL, 1)], held := 1, status := [], now := 0 }

theorem chain1_eq : (Adjudicator.genesis : Adjudicator Nat).deposit (.channel myL) 0 1 = some chain1 := rfl

def net1 : NetworkState Nat p0 := ⟨chain1, [], []⟩

theorem net1_eq : net0.applyAdv apps0 (.land (.deposit (.channel myL) 0 1)) = net1 := rfl

theorem net1_reach : (Nitro.participant apps0 (turboT p0)).Reachable net1 := by
  rw [← net1_eq]
  exact Machine.Reachable.tail net0_reach (Or.inr (Or.inr (Or.inr ⟨.channel myL, 0, 1, rfl⟩)))

-- Step 2: `p0` sends `stV`, the turn-0 state of `myV`. `myV` has the one participant `p0`, so
-- this is the all-signed pre-fund state that `p0` must hold before it signs a state that funds
-- `myV` (`HonestSend.fundsCommitted`).
def net1V : NetworkState Nat p0 := { net1 with sent := [ssV] }

theorem net1V_eq : net1.applyHonest (HonestMove.send stV) = net1V := rfl

theorem net1V_reach : (Nitro.participant apps0 (turboT p0)).Reachable net1V := by
  rw [← net1V_eq]
  exact Machine.Reachable.tail net1_reach
    (Or.inl ⟨HonestMove.send stV, by honest_send, rfl⟩)

-- Step 3: `p0` sends `stL`, the final state of `myL`, which funds `myV`.
def net2 : NetworkState Nat p0 := { net1 with sent := [ssL, ssV] }

theorem net2_eq : net1V.applyHonest (HonestMove.send stL) = net2 := rfl

theorem net2_reach : (Nitro.participant apps0 (turboT p0)).Reachable net2 := by
  rw [← net2_eq]
  exact Machine.Reachable.tail net1V_reach
    (Or.inl ⟨HonestMove.send stL, (HonestMove.Feasible_send _ _ _).mpr ⟨by decide, by decide,
      fundsCommitted_one myV (by decide)
        ⟨ssV, holds_intro _ _ (by decide) (fun _ h => by cases h), by decide, rfl, rfl⟩,
      fun h => absurd h (by decide), by decide, by decide⟩, rfl⟩)

-- Step 4: `p0` lands `conclude myL ssL`, alone (`myL.participants = [p0]`).
def opConL : Op Nat := .conclude myL ssL

theorem net2_holds_ssL : net2.Holds ssL := by
  refine ⟨?_, ?_⟩
  · intro q hq
    simp only [ssL, List.mem_singleton] at hq
    subst hq
    exact Or.inl ⟨rfl, ssL, by simp [net2, ssL], rfl⟩
  · intro v hv
    simp [ssL, stL, State.voucher?] at hv

theorem opConL_feasible : opConL.HonestFeasible net2 := by
  have h := net2_holds_ssL
  simpa [Op.HonestFeasible, Op.proofStates, opConL] using h

def chain3 : Adjudicator Nat :=
  chain1.setStatus myL (.finalized 0 (.allocation [entryV]) (.allocation [entryV]))

theorem chain1_conclude : chain1.apply apps0 p0 opConL = some chain3 := rfl

def net3 : NetworkState Nat p0 := { chain := chain3, sent := [ssL, ssV], received := [ssL] }

theorem net3_eq : net2.applyAdv apps0 (.land opConL) = net3 := rfl

theorem net3_reach : (Nitro.participant apps0 (turboT p0)).Reachable net3 := by
  rw [← net3_eq]
  exact Machine.Reachable.tail net2_reach (Or.inr (Or.inl ⟨opConL, opConL_feasible, rfl⟩))

-- Step 5: `p0` lands `conclude myV ssV`, alone (`myV.participants = [p0]`).
def opConV : Op Nat := .conclude myV ssV

theorem net3_holds_ssV : net3.Holds ssV := by
  refine ⟨?_, ?_⟩
  · intro q hq
    simp only [ssV, List.mem_singleton] at hq
    subst hq
    exact Or.inl ⟨rfl, ssV, by simp [net3, ssV], rfl⟩
  · intro v hv
    simp [ssV, stV, State.voucher?] at hv

theorem opConV_feasible : opConV.HonestFeasible net3 := by
  have h := net3_holds_ssV
  simpa [Op.HonestFeasible, Op.proofStates, opConV] using h

def chain5 : Adjudicator Nat :=
  chain3.setStatus myV (.finalized 0 (.allocation [entryD]) (.allocation [entryD]))

theorem chain3_conclude : chain3.apply apps0 p0 opConV = some chain5 := rfl

def net5 : NetworkState Nat p0 := { chain := chain5, sent := [ssL, ssV], received := [ssV, ssL] }

theorem net5_eq : net3.applyAdv apps0 (.land opConV) = net5 := rfl

theorem net5_reach : (Nitro.participant apps0 (turboT p0)).Reachable net5 := by
  rw [← net5_eq]
  exact Machine.Reachable.tail net3_reach (Or.inr (Or.inl ⟨opConV, opConV_feasible, rfl⟩))

/-! ## `chain5` is a DAG whose Turbo value at `myD` is `1`. -/

theorem chain5_status_eq : chain5.status =
    [(myV, ChannelStatus.finalized 0 (Outcome.allocation [entryD]) (Outcome.allocation [entryD])),
     (myL, ChannelStatus.finalized 0 (Outcome.allocation [entryV]) (Outcome.allocation [entryV]))] := rfl

theorem chain5_statusOf_L :
    chain5.statusOf myL = .finalized 0 (.allocation [entryV]) (.allocation [entryV]) := by decide

theorem chain5_statusOf_V :
    chain5.statusOf myV = .finalized 0 (.allocation [entryD]) (.allocation [entryD]) := by decide

theorem chain5_finalOutcome_L : chain5.finalOutcome (.channel myL) = some (.allocation [entryV]) := by decide

theorem chain5_finalOutcome_V : chain5.finalOutcome (.channel myV) = some (.allocation [entryD]) := by decide

theorem chain5_allocationOf_L : chain5.allocationOf (.channel myL) = [entryV] := by decide

theorem chain5_allocationOf_V : chain5.allocationOf (.channel myV) = [entryD] := by decide

theorem chain5_allocationOf_other (c : FixedPart) (hL : c ≠ myL) (hV : c ≠ myV) :
    chain5.allocationOf (.channel c) = [] := by
  have hstat : chain5.statusOf c = .open 0 := by
    unfold Adjudicator.statusOf
    rw [chain5_status_eq]
    simp only [List.lookup]
    split
    · next hb => exact absurd (beq_iff_eq.mp hb) hV
    · split
      · next hb => exact absurd (beq_iff_eq.mp hb) hL
      · rfl
  simp [Adjudicator.allocationOf, Adjudicator.finalOutcome, hstat, ChannelStatus.finalOutcome]

theorem chain5_allocationOf_external (d : Nat) : chain5.allocationOf (.external d) = [] := by
  simp [Adjudicator.allocationOf, Adjudicator.finalOutcome]

/-- The only edge of `chain5` is `myL.address → myV.address`. -/
theorem chain5_edge_iff (x y : Address Nat) :
    chain5.Edge x y ↔ x = Address.channel myL ∧ y = Address.channel myV := by
  constructor
  · rintro ⟨hyext, e, he, hed⟩
    cases x with
    | external dx => simp [chain5_allocationOf_external] at he
    | channel cx =>
      by_cases hL : cx = myL
      · subst hL
        rw [chain5_allocationOf_L, List.mem_singleton] at he
        subst he
        exact ⟨rfl, hed ▸ rfl⟩
      · by_cases hV : cx = myV
        · subst hV
          rw [chain5_allocationOf_V, List.mem_singleton] at he
          subst he
          exfalso
          rw [← hed] at hyext
          simp [entryD, alloc, myD, Address.isExternal] at hyext
        · rw [chain5_allocationOf_other cx hL hV] at he
          exact absurd he (by simp)
  · rintro ⟨rfl, rfl⟩
    exact ⟨rfl, entryV, chain5_allocationOf_L ▸ List.mem_singleton_self _, rfl⟩

theorem chain5_transGen (x y : Address Nat) (h : Relation.TransGen chain5.Edge x y) :
    x = Address.channel myL ∧ y = Address.channel myV := by
  induction h with
  | single hxy => exact (chain5_edge_iff _ _).1 hxy
  | tail _ hyz ih =>
    exfalso
    obtain ⟨-, hb⟩ := ih
    obtain ⟨hb', -⟩ := (chain5_edge_iff _ _).1 hyz
    exact myL_ne_myV (channel_inj (hb.symm.trans hb')).symm

theorem chain5_dag : chain5.IsDAG := by
  refine ⟨fun a h => ?_⟩
  obtain ⟨ha, hb⟩ := chain5_transGen a a h
  exact myL_ne_myV (channel_inj (ha.symm.trans hb))

theorem myL_addr_ne_myV_addr : (Address.channel myL : Address Nat) ≠ Address.channel myV :=
  fun h => myL_ne_myV (channel_inj h)

theorem chain5_balances_other (n : Address Nat) (hn : n ≠ Address.channel myL) :
    chain5.balances.get n = 0 := by
  have hbal : chain5.balances = chain1.balances := rfl
  rw [hbal]
  cases n with
  | external d => rfl
  | channel c =>
    have hcL : c ≠ myL := fun h => hn (by rw [h])
    simp only [chain1, Balances.get, List.lookup]
    split
    · next hb => exact absurd (channel_inj (beq_iff_eq.mp hb)) hcL
    · rfl

theorem chain5_topo : chain5.IsTopologicalOrder [Address.channel myL, Address.channel myV] := by
  refine ⟨?_, ?_, ?_⟩
  · simp [List.nodup_cons, myL_ne_myV]
  · intro n d hed
    obtain ⟨rfl, rfl⟩ := (chain5_edge_iff n d).1 hed
    exact ⟨0, 1, rfl, rfl, by decide⟩
  · intro n hn
    by_cases h1 : n = Address.channel myL
    · simp [h1]
    by_cases h2 : n = Address.channel myV
    · simp [h2]
    exfalso
    rcases hn with hn1 | hn2
    · exact hn1 (chain5_balances_other n h1)
    · apply hn2
      cases n with
      | external d => exact chain5_allocationOf_external d
      | channel c =>
        have hL : c ≠ myL := fun h => h1 (by rw [h])
        have hV : c ≠ myV := fun h => h2 (by rw [h])
        exact chain5_allocationOf_other c hL hV

/-- The Turbo value at `myD` is `1`: deposited at `myL`, fully redistributed
    through `myV`. -/
theorem chain5_turboValue : chain5.TurboValue myD 1 := by
  refine ⟨[Address.channel myL, Address.channel myV], chain5_topo, ?_⟩
  decide

/-! ## `chain5` is a fixed point under any transfer-only play. -/

/-- No transfer on `chain5` ever succeeds: the only entry anywhere names the
    non-`fundable` `myV.address`. -/
theorem chain5_transfer_none (a : FixedPart) (b : Address Nat) : chain5.transfer a b = none := by
  cases h : chain5.transfer a b with
  | none => rfl
  | some s' =>
    exfalso
    obtain ⟨o, amt, x, hfo, hfind, -, -, -, -, -, hak, hbf⟩ := Adjudicator.transfer_some h
    by_cases hV : a = myV
    · subst hV; simp [myV] at hak
    · by_cases hL : a = myL
      · subst hL
        rw [FixedPart.address_eq, chain5_finalOutcome_L] at hfo
        simp only [Option.some.injEq, Outcome.allocation.injEq] at hfo
        subst hfo
        have hbV : (Address.channel myV : Address Nat) = b := by
          by_contra hne
          simp [Allocation.find, List.find?, entryV, alloc, hne] at hfind
        rw [← hbV] at hbf
        simp [Address.fundable, myV] at hbf
      · have hao := chain5_allocationOf_other a hL hV
        rw [FixedPart.address_eq] at hfo
        unfold Adjudicator.allocationOf at hao
        rw [hfo] at hao
        have hoeq : o = [] := by
          cases o with
          | nil => rfl
          | cons e rest => simp [Allocation.dedup, Allocation.dedupFrom] at hao
        rw [hoeq] at hfind
        simp [Allocation.find] at hfind

/-- `applyAll` of any transfer-only list leaves `chain5` unchanged. -/
theorem chain5_applyAll_fixed (apps : Apps Nat) (ops : List (Participant × Op Nat))
    (hops : OnlyTransfers ops) : Adjudicator.applyAll apps ops chain5 = chain5 := by
  induction ops with
  | nil => rfl
  | cons o rest ih =>
    obtain ⟨a, b, ho⟩ := hops o List.mem_cons_self
    obtain ⟨caller, op⟩ := o
    simp only at ho
    subst ho
    simp only [Adjudicator.applyAll, Adjudicator.apply, chain5_transfer_none, Option.getD_none]
    exact ih (fun e he => hops e (List.mem_cons_of_mem _ he))

theorem IsTransfer_shape {m : HonestMove Nat} (hm : HonestMove.IsTransfer m) :
    ∃ a b, m = HonestMove.chain (.transfer a b) := by
  cases m with
  | react r =>
    obtain ⟨a, b, hc, hs⟩ := hm
    refine ⟨a, b, ?_⟩
    simp only [HonestMove.chain, Reaction.one]
    cases r with
    | mk calls sends => simp_all
  | wait dt => simp [HonestMove.IsTransfer] at hm

theorem not_canObtain :
    ¬ CanObtainIn apps0 (turboT p0) HonestMove.IsTransfer myD 1 net5 := by
  intro h
  have key : ∀ net' : NetworkState Nat p0,
      UnbeatableIn apps0 (turboT p0) HonestMove.IsTransfer
        (fun net'' => 1 ≤ net''.chain.balances.get myD) net' →
      net'.chain = chain5 → False := by
    intro net' hU
    induction hU with
    | done hG =>
      intro hinv
      rw [hinv] at hG
      revert hG
      decide
    | @move netC m hallowed hfeas hrec ih =>
      intro hinv
      obtain ⟨a, b, hmeq⟩ := IsTransfer_shape hallowed
      subst hmeq
      obtain ⟨net'', hround⟩ := Threat.Round.exists (turboT p0) hfeas
      apply ih net'' hround
      rw [NetworkState.applyHonest_chain]
      obtain ⟨n1, h1, h2⟩ := Threat.Round.single hround
      obtain ⟨A1, hA1, e1⟩ := h1.transfers (turboT_only p0)
      obtain ⟨A2, hA2, e2⟩ := h2.transfers (turboT_only p0)
      have hland : (n1.applyAdv apps0 (.land (.transfer a b))).chain =
          Adjudicator.applyAll apps0 [(p0, .transfer a b)] n1.chain := by
        simp only [NetworkState.applyAdv]
        cases hap : n1.chain.apply apps0 p0 (.transfer a b) <;> simp [Adjudicator.applyAll, hap]
      have hchain : net''.chain =
          Adjudicator.applyAll apps0 (A1 ++ (p0, .transfer a b) :: A2) netC.chain := by
        rw [e2, hland, e1, ← Adjudicator.applyAll_append, ← Adjudicator.applyAll_append]
        rfl
      have hall : OnlyTransfers (A1 ++ (p0, .transfer a b) :: A2) := by
        intro e he
        rcases List.mem_append.1 he with he | he
        · exact hA1 e he
        · rcases List.mem_cons.1 he with rfl | he
          · exact ⟨a, b, rfl⟩
          · exact hA2 e he
      rw [hchain, hinv]
      exact chain5_applyAll_fixed apps0 _ hall
  exact key net5 h rfl

/-- Every hypothesis of the unconstrained `turbo_value_achievable` (before the
    `TurboOutcomeNetwork` migration) holds for this witness and its
    conclusion fails. Kept for the record; the current `turbo_value_achievable`
    no longer takes these hypotheses (see `chain5_not_turboOutcomeNetwork`
    below). -/
theorem turbo_value_achievable_false :
    ¬ ∀ (apps : Apps Nat) (p : Participant) (T : Threat Nat p) (_B : Bounds apps p T)
        (_hT : T.TransfersOnly) (_hcap : T.CapableTransfers)
        (net : NetworkState Nat p) (_hr : (Nitro.participant apps T).Reachable net)
        (_hdag : net.chain.IsDAG) (d : Nat) (v : Coins)
        (_hv : net.chain.TurboValue (.external d) v),
        CanObtainIn apps T HonestMove.IsTransfer (.external d) v net := by
  intro h
  exact not_canObtain (h apps0 p0 (turboT p0) (turboT_bounds apps0 p0) (turboT_only p0)
    (turboT_capable p0) net5 net5_reach chain5_dag 0 1 chain5_turboValue)

/-! ## The resolution: `chain5` is not a `TurboOutcomeNetwork` -/

/-- `myV` is a Turbo-scope source (`chain5_allocationOf_V`: it carries the
    allocation `[entryD]`, so its `allocationOf` is not `[]`) that is not a
    ledger channel (`myV.kind = .virtual`). `TurboScope`'s first conjunct,
    applied to `myV`, is therefore false, so `chain5.TurboScope` is false:
    `chain5` no longer satisfies the Turbo scope the refined
    `turbo_value_achievable` requires. -/
theorem chain5_not_turboScope : ¬ chain5.TurboScope := by
  rintro ⟨hsrc, -⟩
  have hne : chain5.allocationOf (.channel myV) ≠ [] := by rw [chain5_allocationOf_V]; decide
  exact absurd (hsrc myV hne) (by decide)

/-- `chain5` is not a `TurboOutcomeNetwork`: it is a DAG (`chain5_dag`) but
    not in Turbo scope (`chain5_not_turboScope`). The counterexample no
    longer applies to the migrated `turbo_value_achievable`: its premise
    `net.chain.IsTurboOutcomeNetwork` fails at `chain5`. -/
theorem chain5_not_turboOutcomeNetwork : ¬ chain5.IsTurboOutcomeNetwork :=
  fun ⟨_, hscope⟩ => chain5_not_turboScope hscope

end ArmadaLean.Nitro.Counterexample
