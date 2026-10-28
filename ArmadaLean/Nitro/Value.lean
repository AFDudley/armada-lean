/-
  Nitro protocol specification: the network of outcomes and the Turbo Value
  Algorithm (Nitro:818-835).
  See `Address.lean` for the source list. SATP and go-nitro have no value
  algorithm, so Nitro is the primary source for this file. The Nitro
  Lower-bound Value Algorithm (Nitro:1178-1255) reads Nitro's `claim`, which
  SATP and go-nitro replaced by `reclaim`; it is not modelled (operator
  ruling 2026-10-27).

  DAG (operator ruling 2026-10-27). "The network of outcomes is a DAG" means
  "no channel can reach itself by following edges": `Acyclic s.Edge`, with
  core Lean's `Relation.TransGen`. Nitro:796-799 chooses a topological
  ordering; a proof that needs one derives it as a lemma. No theorem type
  carries an ordering: the algorithm's result is the relation
  `Adjudicator.TurboValue`.
-/
import Mathlib.Logic.Relation
import ArmadaLean.Nitro.Strategy

namespace ArmadaLean.Nitro

variable {E : Type} [DecidableEq E]

/-- The stored allocation of a node, with duplicate destinations dropped
    (Nitro:744-746). A node with no finalized allocation has the empty
    allocation. -/
def Adjudicator.allocationOf (s : Adjudicator E) (n : Address E) : Allocation E :=
  match s.finalOutcome n with
  | some (.allocation o) => o.dedup
  | _ => []

/-- Nitro:790-792: "the nodes are channels and the edges represent allocations
    from one channel to the other." `edge n d`: `n`'s outcome allocates to
    channel `d`. -/
def Adjudicator.Edge (s : Adjudicator E) (n d : Address E) : Prop :=
  d.isExternal = false ∧ ∃ e ∈ s.allocationOf n, e.dest = d

/-- A relation with no cycle: no node reaches itself by one or more steps,
    `∀ c, ¬ Relation.TransGen edge c c` (operator ruling 2026-10-27), stated
    as `Std.Irrefl` of the transitive closure (Mathlib `Relation.TransGen`,
    core `Std.Irrefl`; its `irrefl` field is the ruling's formula). -/
def Acyclic {α : Type} (edge : α → α → Prop) : Prop :=
  Std.Irrefl (Relation.TransGen edge)

/-- Nitro:796-798: "A topological ordering is an ordering of nodes such that, if
    N1 ↦ N2 is an edge, then N1 < N2." Every node with a balance or an
    allocation appears once. -/
def Adjudicator.IsTopologicalOrder (s : Adjudicator E) (order : List (Address E)) : Prop :=
  order.Nodup ∧
  (∀ n d, s.Edge n d → ∃ i j : Nat, order[i]? = some n ∧ order[j]? = some d ∧ i < j) ∧
  (∀ n, (s.balances.get n ≠ 0 ∨ s.allocationOf n ≠ []) → n ∈ order)

/-- Nitro:790-795: "We will only consider the case where the network of
    outcomes forms a directed acyclic graph (DAG)". -/
def Adjudicator.IsDAG (s : Adjudicator E) : Prop :=
  Acyclic s.Edge

/-- Nitro:824-834, step 3: pay `remaining` through one node's allocation in
    order; each destination's value rises by `min(payout, remaining)`. A
    guarantee item takes its place in the priority order but credits no
    one: `transfer` cannot pay a guarantee (go-nitro MultiAssetHolder.sol:169-170,
    "cannot transfer a guarantee"), and the Turbo game has no `reclaim`. -/
def payoutValues : Balances E → Coins → Allocation E → Balances E
  | vals, _, [] => vals
  | vals, remaining, e :: rest =>
    let x := min e.amount remaining
    payoutValues (if e.item.isGuarantee then vals else vals.add e.dest x) (remaining - x) rest

/-- Nitro:818-835 Turbo Value Algorithm, steps 2-3: start from the balances,
    then for each node in order pay its value through its allocation. -/
def Adjudicator.turboValues (s : Adjudicator E) : List (Address E) → Balances E → Balances E
  | [], vals => vals
  | n :: rest, vals => s.turboValues rest (payoutValues vals (vals.get n) (s.allocationOf n))

/-- Nitro:835 step 4: "Then Values[n] gives the value of node n." -/
def Adjudicator.turboValueAlong (s : Adjudicator E) (order : List (Address E)) (n : Address E) :
    Coins :=
  (s.turboValues order s.balances).get n

/-- Nitro:818-835: `x` is the Turbo Value Algorithm's value of `n` for some
    topological ordering (step 1). The ordering is chosen here, not in a
    theorem type. -/
def Adjudicator.TurboValue (s : Adjudicator E) (n : Address E) (x : Coins) : Prop :=
  ∃ order, s.IsTopologicalOrder order ∧ s.turboValueAlong order n = x

/-- A transfer sequence is maximal when no further transfer moves coins.
    Nitro:840-842: "we have done every possible transfer on these
    channels". go-nitro's `transfer` pays the whole affordable amount, so a
    further transfer moves coins only if some entry still affords a
    positive amount. -/
def Adjudicator.TransferExhausted (s : Adjudicator E) : Prop :=
  ∀ a b s', s.transfer a b = some s' → s'.balances = s.balances

/-- A list of transfers only. -/
def OnlyTransfers (ops : List (Participant × Op E)) : Prop :=
  ∀ e ∈ ops, ∃ a b, e.2 = Op.transfer a b

/-- An honest transfer move: the moves of the Turbo game (Nitro:779-781,
    "strategies and counter-strategies involving transfer operations only"). -/
def HonestMove.IsTransfer : HonestMove E → Prop
  | .chain (.transfer _ _) => True
  | _ => False

/-- Nitro:779-781: the adversary of the Turbo game plays transfers only
    (go-nitro `transfer`). The clock does not move. -/
def Threat.TransfersOnly {p : Participant} (T : Threat E p) : Prop :=
  ∀ net m, T.feasible net m → ∃ caller a b, m = .chain caller (.transfer a b)

/-- The capability of the Turbo adversary: every transfer by another
    participant is feasible (Nitro:460-461 with Nitro:779-781). -/
def Threat.CapableTransfers {p : Participant} (T : Threat E p) : Prop :=
  ∀ net caller a b, caller ≠ p → T.feasible net (.chain caller (.transfer a b))

end ArmadaLean.Nitro
