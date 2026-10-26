/-
  Nitro protocol specification: the network of outcomes, the Turbo Value
  Algorithm (Nitro:818-835) and the Nitro Lower-bound Value Algorithm
  (Nitro:1178-1255). See `Address.lean` for the source list. SATP and
  go-nitro have no value algorithm, so Nitro is the primary source for this
  file. The lower-bound algorithm reads Nitro's `claim`, which SATP and
  go-nitro replaced by `reclaim`.

  Modelling choice (DAG). Nitro:796-799 takes a topological ordering of the
  outcome network and notes that every DAG has one. Here "the network is a
  DAG" is "a topological ordering exists" (`Adjudicator.IsDAG`).
-/
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
    from one channel to the other." -/
def Adjudicator.Edge (s : Adjudicator) (n d : Address) : Prop :=
  ∃ e ∈ s.allocationOf n, e.dest = d

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
  ∃ order, s.IsTopologicalOrder order

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
def Adjudicator.turboValue (s : Adjudicator) (order : List Address) (n : Address) : Coins :=
  (s.turboValues order s.balances).get n

/-- A Turbo state: every finalized outcome is an allocation (Nitro:732). -/
def Adjudicator.TurboOnly (s : Adjudicator) : Prop :=
  ∀ c t pr, s.finalOutcome (.channel c) ≠ some (.guarantee t pr)

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

/-- Nitro:1203-1209: an allocation channel `L` and the guarantees `G1..Gn`
    that target it, with values `v_i` and the priority lists that induce the
    permutations `π_i`. -/
structure GuaranteeGroup where
  target : Allocation
  guarantees : List (Coins × List Address)

/-- Nitro:1217 `Σ v_i`. -/
def GuaranteeGroup.funds (g : GuaranteeGroup) : Coins :=
  (g.guarantees.map (·.1)).sum

/-- Nitro:1216-1217: "If Σ v_i > Σ a_j, then we say the system is overfunded." -/
def GuaranteeGroup.Overfunded (g : GuaranteeGroup) : Prop :=
  g.target.total < g.funds

/-- Nitro:1251-1252: "the fully funded case, where Σ v_i = Σ a_j". -/
def GuaranteeGroup.FullyFunded (g : GuaranteeGroup) : Prop :=
  g.funds = g.target.total

/-- One claim inside the group: guarantee `i` pays `x` to `d` (Nitro:1139-1145,
    restricted to the group). -/
def GuaranteeGroup.claim (g : GuaranteeGroup) (i : Nat) (d : Address) (x : Coins) :
    Option GuaranteeGroup :=
  match g.guarantees[i]? with
  | some (v, pr) =>
    if GuaranteeAffords v pr g.target d x then
      some { target := g.target.reduceOwed d x, guarantees := g.guarantees.set i (v - x, pr) }
    else
      none
  | none => none

/-- Apply a list of claims. A failed claim changes nothing. -/
def GuaranteeGroup.applyClaims : List (Nat × Address × Coins) → GuaranteeGroup → GuaranteeGroup
  | [], g => g
  | (i, d, x) :: rest, g => GuaranteeGroup.applyClaims rest ((g.claim i d x).getD g)

/-- Nitro:1219-1221 (constraint 19): "no funds are left in the guarantees". No
    positive claim can succeed. -/
def GuaranteeGroup.Exhausted (g : GuaranteeGroup) : Prop :=
  ∀ i d x, 0 < x → g.claim i d x = none

/-- The amount a destination received: the fall of what the target owes it. -/
def GuaranteeGroup.paidTo (g g' : GuaranteeGroup) (d : Address) : Coins :=
  g.target.owed d - g'.target.owed d

/-- Nitro:1202-1207 Minimum Payout Calculation: "the minimum payout, `p_i`, that
    each destination will receive when all possible payout orders are
    considered." `m` is the least amount `d` receives over every exhausted
    claim order. -/
def GuaranteeGroup.IsMinPayout (g : GuaranteeGroup) (d : Address) (m : Coins) : Prop :=
  (∀ cs, (g.applyClaims cs).Exhausted → m ≤ g.paidTo (g.applyClaims cs) d) ∧
  (∃ cs, (g.applyClaims cs).Exhausted ∧ g.paidTo (g.applyClaims cs) d = m)

/-- The guarantees that target `l`, with their current values. -/
def Adjudicator.guaranteesTargeting (s : Adjudicator) (vals : Balances) (l : Address) :
    List (Coins × List Address) :=
  s.status.filterMap (fun e =>
    match e.2.finalOutcome s.now with
    | some (.guarantee t pr) => if t = l then some (vals.get e.1.address, pr) else none
    | _ => none)

/-- Nitro:1210-1215: the group of `l`. "We will assume the value of L itself is
    0 ... by adding a guarantee G_{n+1} that has value x, that targets L and
    that has π_{n+1}(k) = k." The empty priority list is the identity. -/
def Adjudicator.groupOf (s : Adjudicator) (vals : Balances) (l : Address) : GuaranteeGroup :=
  { target := s.allocationOf l,
    guarantees := s.guaranteesTargeting vals l ++
      (if 0 < vals.get l then [(vals.get l, [])] else []) }

/-- Nitro:1178-1193 Nitro Lower-bound Value Algorithm, step 3: a guarantee node
    does nothing; an allocation node adds `MinPayouts[d]` to each destination
    `d`. `minPayout` is a function that meets `IsMinPayout`. -/
def Adjudicator.nitroValues (s : Adjudicator) (minPayout : GuaranteeGroup → Address → Coins) :
    List Address → Balances → Balances
  | [], vals => vals
  | n :: rest, vals =>
    match s.finalOutcome n with
    | some (.guarantee _ _) => s.nitroValues minPayout rest vals
    | _ =>
      let g := s.groupOf vals n
      s.nitroValues minPayout rest
        ((s.allocationOf n).foldl (fun acc e => acc.add e.dest (minPayout g e.dest)) vals)

/-- Nitro:1193 step 4: `Values[n]`. -/
def Adjudicator.nitroValue (s : Adjudicator) (minPayout : GuaranteeGroup → Address → Coins)
    (order : List Address) (n : Address) : Coins :=
  (s.nitroValues minPayout order s.balances).get n

/-- `minPayout` meets the Minimum Payout Calculation on every group. -/
def MinPayoutCorrect (minPayout : GuaranteeGroup → Address → Coins) : Prop :=
  ∀ (g : GuaranteeGroup) (d : Address), g.IsMinPayout d (minPayout g d)

end ArmadaLean.Nitro
