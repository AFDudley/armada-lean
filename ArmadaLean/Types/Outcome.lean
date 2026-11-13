/-
  Refined outcome types. `docs/lean/typed-library.md` §4, row `Outcome.lean`.
  Each type replaces a loose `Prop` hypothesis that more than one Nitro
  statement repeated, or (`TurboOutcomeNetwork`) a hypothesis the counterexample
  `docs/counterexamples/turbo_value_achievable.lean` shows is
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

/-- Turbo scope (Nitro:732-734 and footnote 5, Nitro:1102-1104; design
    decision 2026-10-31): every channel that is a node of the outcome network
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
    `docs/counterexamples/turbo_value_achievable.lean`,
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

end ArmadaLean.Nitro
