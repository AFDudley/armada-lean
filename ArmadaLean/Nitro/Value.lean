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

/-- The finalized allocation of a node, with duplicate destinations dropped
    (Nitro:744-746). A node with no finalized allocation has the empty
    allocation. -/
def Adjudicator.allocationOf (s : Adjudicator) (n : Address) : Allocation :=
  match s.finalOutcome n with
  | some (.allocation o) => o.dedup
  | _ => []

/-- Nitro:790-792: "the nodes are channels and the edges represent allocations
    from one channel to the other." `edge n d`: `n`'s outcome allocates to
    channel `d`. -/
def Adjudicator.Edge (s : Adjudicator) (n d : Address) : Prop :=
  d.isParticipant = false ∧ ∃ e ∈ s.allocationOf n, e.dest = d

/-- A relation with no cycle: no node reaches itself by one or more steps,
    `∀ c, ¬ Relation.TransGen edge c c` (operator ruling 2026-10-27), stated
    as `Std.Irrefl` of the transitive closure (Mathlib `Relation.TransGen`,
    core `Std.Irrefl`; its `irrefl` field is the ruling's formula). -/
def Acyclic {α : Type} (edge : α → α → Prop) : Prop :=
  Std.Irrefl (Relation.TransGen edge)

/-- Nitro:796-798: "A topological ordering is an ordering of nodes such that, if
    N1 ↦ N2 is an edge, then N1 < N2." Every node with a balance or an
    allocation appears once. -/
def Adjudicator.IsTopologicalOrder (s : Adjudicator) (order : List Address) : Prop :=
  order.Nodup ∧
  (∀ n d, s.Edge n d → ∃ i j : Nat, order[i]? = some n ∧ order[j]? = some d ∧ i < j) ∧
  (∀ n, (s.balances.get n ≠ 0 ∨ s.allocationOf n ≠ []) → n ∈ order)

/-- Nitro:790-795: "We will only consider the case where the network of
    outcomes forms a directed acyclic graph (DAG)". -/
def Adjudicator.IsDAG (s : Adjudicator) : Prop :=
  Acyclic s.Edge

/-- Nitro:824-834, step 3: pay `remaining` through one node's allocation in
    order; each destination's value rises by `min(payout, remaining)`. -/
def payoutValues : Balances → Coins → Allocation → Balances
  | vals, _, [] => vals
  | vals, remaining, e :: rest =>
    let x := min e.amount remaining
    payoutValues (vals.add e.dest x) (remaining - x) rest

/-- Nitro:818-835 Turbo Value Algorithm, steps 2-3: start from the balances,
    then for each node in order pay its value through its allocation. -/
def Adjudicator.turboValues (s : Adjudicator) : List Address → Balances → Balances
  | [], vals => vals
  | n :: rest, vals => s.turboValues rest (payoutValues vals (vals.get n) (s.allocationOf n))

/-- Nitro:835 step 4: "Then Values[n] gives the value of node n." -/
def Adjudicator.turboValueAlong (s : Adjudicator) (order : List Address) (n : Address) : Coins :=
  (s.turboValues order s.balances).get n

/-- Nitro:818-835: `x` is the Turbo Value Algorithm's value of `n` for some
    topological ordering (step 1). The ordering is chosen here, not in a
    theorem type. -/
def Adjudicator.TurboValue (s : Adjudicator) (n : Address) (x : Coins) : Prop :=
  ∃ order, s.IsTopologicalOrder order ∧ s.turboValueAlong order n = x

/-- A transfer sequence is maximal when no further transfer moves coins.
    Nitro:840-842: "we have done every possible transfer on these
    channels". go-nitro's `transfer` pays the whole affordable amount, so a
    further transfer moves coins only if some entry still affords a
    positive amount. -/
def Adjudicator.TransferExhausted (s : Adjudicator) : Prop :=
  ∀ a b s', s.transfer a b = some s' → s'.balances = s.balances

/-- A list of transfers only. -/
def OnlyTransfers (ops : List (Participant × Op)) : Prop :=
  ∀ e ∈ ops, ∃ a b, e.2 = Op.transfer a b

end ArmadaLean.Nitro
