/-
  Refined outcome types. `docs/lean/typed-library.md` §4, row `Outcome.lean`.
  Each type replaces a loose `Prop` hypothesis that more than one Nitro
  statement repeated, or (`TurboOutcomeNetwork`) a hypothesis the counterexample
  `docs/counterexamples/turbo_value_achievable.lean` (`worker/aln-eb2`) shows is
  too weak as stated.
-/
import ArmadaLean.Nitro.Value

namespace ArmadaLean.Nitro

variable {E : Type} [DecidableEq E]

/-! ## Outcome networks: `DAGOutcomeNetwork`, and `TurboOutcomeNetwork` that extends it

Two levels (operator, 2026-10-31). The outcome network of an on-chain state
(Nitro:790-791: "the nodes are channels and the edges represent" allocations)
is a DAG for `DAGOutcomeNetwork`. `TurboOutcomeNetwork` extends it with the
Turbo scope. Three theorems are proved for every DAG outcome network,
including networks with guarantees and virtual channels
(`turbo_value_upper_bound`, `turbo_order_independent`,
`turbo_value_exists_unique`). This is more general than the paper, which
states them inside Turbo (§5.2). The generality is kept on purpose: it
covers simple transfers in a system that also has virtual channels. Only
`turbo_value_achievable` and `turbo_value_is_value` need the Turbo scope
(counterexample `docs/counterexamples/turbo_value_achievable.lean`). -/

/-- Turbo scope (Nitro:732-734 and footnote 5, Nitro:1102-1104; operator
    ruling 2026-10-31): every channel that is a node of the outcome network
    (Nitro:790-791) — a source (it holds an allocation) or a destination (an
    entry names it) — is a ledger channel, never virtual, and no entry is a
    guarantee. -/
def Adjudicator.TurboScope (s : Adjudicator E) : Prop :=
  (∀ c : FixedPart, s.allocationOf (.channel c) ≠ [] → c.kind = .ledger) ∧
  (∀ n : Address E, ∀ e ∈ s.allocationOf n,
    e.item.isGuarantee = false ∧ ∀ c : FixedPart, e.dest = .channel c → c.kind = .ledger)

/-- The fact `TurboOutcomeNetwork` wraps: `s`'s outcome network is a DAG
    and stays in Turbo scope. `docs/lean/typed-library.md` §4, row
    `Outcome.lean`. Reason for the scope conjunct, not just `IsDAG`: on a
    state with a virtual channel, `turbo_value_achievable` is false (the
    counterexample `chain5` of
    `docs/counterexamples/turbo_value_achievable.lean`, `worker/aln-eb2`,
    is a DAG — `chain5_dag` — but its only edge targets a virtual channel,
    so no `transfer` call ever moves a coin, `chain5_transfer_none`). -/
def Adjudicator.IsTurboOutcomeNetwork (s : Adjudicator E) : Prop :=
  s.IsDAG ∧ s.TurboScope

/-- An on-chain state whose outcome network is a DAG (Nitro:790-791). The
    parent of `TurboOutcomeNetwork`; the type of theorems that hold for every
    DAG outcome network (module comment). -/
structure DAGOutcomeNetwork (E : Type) [DecidableEq E] where
  /-- The on-chain state. -/
  chain : Adjudicator E
  /-- Its outcome network is a DAG (Nitro:790-791). -/
  isDAG : chain.IsDAG

namespace DAGOutcomeNetwork

/-- Coercion to the carrier (`writing-lean.md` §3, rule 2 of
    `typed-library.md`). -/
instance : CoeOut (DAGOutcomeNetwork E) (Adjudicator E) := ⟨DAGOutcomeNetwork.chain⟩

@[simp] theorem coe_eq (s : DAGOutcomeNetwork E) : (s : Adjudicator E) = s.chain := rfl

-- No decidable smart constructor: `Adjudicator.IsDAG` (`Acyclic s.Edge`,
-- `Relation.TransGen` over the infinite type `Address E`) carries no
-- `Decidable` instance in `Value.lean` (`typed-library.md` rule 2 makes
-- the constructor conditional on decidability).

end DAGOutcomeNetwork

/-- A DAG outcome network in Turbo scope: only allocations among ledger
    channels and external destinations, with no virtual channels and no
    guarantees (`Adjudicator.TurboScope`, Nitro:732-734 and footnote 5,
    Nitro:1102-1104). `docs/lean/typed-library.md` §4, row `Outcome.lean`. -/
structure TurboOutcomeNetwork (E : Type) [DecidableEq E] extends DAGOutcomeNetwork E where
  /-- Every node is a ledger channel or an external destination, and no entry is a guarantee. -/
  turboScope : chain.TurboScope

namespace TurboOutcomeNetwork

/-- A Turbo network is a DAG network (`extends`). -/
instance : CoeOut (TurboOutcomeNetwork E) (DAGOutcomeNetwork E) := ⟨toDAGOutcomeNetwork⟩

/-- Coercion to the carrier. -/
instance : CoeOut (TurboOutcomeNetwork E) (Adjudicator E) := ⟨fun s => s.chain⟩

@[simp] theorem coe_eq (s : TurboOutcomeNetwork E) : (s : Adjudicator E) = s.chain := rfl

theorem isTurboOutcomeNetwork (s : TurboOutcomeNetwork E) : s.chain.IsTurboOutcomeNetwork :=
  ⟨s.isDAG, s.turboScope⟩

end TurboOutcomeNetwork

/-! ## The `hog` rule of `satp_end_user_recovers`: every guarantee peer is external -/

/-- The fact the `hog` hypothesis of `satp_end_user_recovers` names: every
    guarantee entry of `o` lists only external peers, never a channel.
    Operator ruling 2026-10-31 (`aln-223` counterexample,
    `docs/counterexamples/satp_end_user_recovers.lean`): a guarantee whose
    peer is a channel address (`gX`, that file) lets the adversary keep the
    channel from ever finalizing with no entry for it, so end-user recovery
    needs this fact. -/
def Allocation.GuaranteesExternal (o : Allocation E) : Prop :=
  ∀ e ∈ o, ∀ x ps, e.item = .guarantee x ps → ∀ d ∈ ps, d.isExternal = true

/-- `Entry.GuaranteesExternal`, restated by matching on `e.item` instead of
    quantifying over every `x`/`ps` it could equal: decidable, since the
    quantifier then ranges over the one list `ps` the match already names. -/
private def Entry.GuaranteesExternalB (e : Entry E) : Bool :=
  match e.item with
  | .guarantee _ ps => ps.all (·.isExternal)
  | .alloc _ => true

omit [DecidableEq E] in
private theorem entry_guaranteesExternal_iff (e : Entry E) :
    (∀ x ps, e.item = .guarantee x ps → ∀ d ∈ ps, d.isExternal = true) ↔
      e.GuaranteesExternalB = true := by
  unfold Entry.GuaranteesExternalB
  cases h : e.item with
  | alloc a => simp
  | guarantee x ps => simp [List.all_eq_true]

instance (o : Allocation E) : Decidable o.GuaranteesExternal :=
  decidable_of_iff (∀ e ∈ o, e.GuaranteesExternalB = true)
    (forall_congr' fun e => forall_congr' fun _ => (entry_guaranteesExternal_iff e).symm)

/-- An allocation whose guarantee entries, if any, name only external peers
    (`Allocation.GuaranteesExternal`, the `hog` rule of
    `satp_end_user_recovers`). `docs/lean/typed-library.md` §4, row
    `Outcome.lean`. -/
def GuaranteedOutcome (E : Type) [DecidableEq E] : Type := {o : Allocation E // o.GuaranteesExternal}

namespace GuaranteedOutcome

/-- Coercion to the carrier (`writing-lean.md` §3, rule 2 of
    `typed-library.md`). -/
instance : CoeOut (GuaranteedOutcome E) (Allocation E) := ⟨Subtype.val⟩

@[simp] theorem guarantees_external (o : GuaranteedOutcome E) :
    (o : Allocation E).GuaranteesExternal := o.property

/-- Decidable smart constructor (`typed-library.md` rule 2). -/
def ofAllocation? (o : Allocation E) : Option (GuaranteedOutcome E) :=
  if h : o.GuaranteesExternal then some ⟨o, h⟩ else none

@[simp] theorem ofAllocation?_eq_some_iff {o : Allocation E} {g : GuaranteedOutcome E} :
    ofAllocation? o = some g ↔ (g : Allocation E) = o := by
  unfold ofAllocation?
  split
  · constructor
    · intro h; cases h; rfl
    · intro h; cases g with
      | mk go hgo => cases h; rfl
  · constructor
    · intro h; cases h
    · intro h; subst h; rename_i hcon; exact absurd g.property hcon

end GuaranteedOutcome

end ArmadaLean.Nitro
