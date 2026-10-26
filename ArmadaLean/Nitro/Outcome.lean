/-
  Nitro protocol specification: outcomes, allocations, guarantees, and the
  priority-order payout. See `Address.lean` for the source list.

  Modelling choice (two guarantee forms). S2 §6.1 (1070-1074) gives a
  guarantee as the outcome of a whole channel: a target and a priority list.
  S3:322-323 gives a guarantee as one item inside an allocation:
  `G(x, [A, B])`. S4 (research-papers page) says S3 replaced guarantee
  channels with the richer outcome format. Both forms are here. The S2 form is
  `Outcome.guarantee`. The S3 form is `Item.guarantee` inside an allocation.
-/
import ArmadaLean.Nitro.Address

namespace ArmadaLean.Nitro

/-- One outcome item. S3:320-325: an allocation `A(a)` is an amount paid to
    a destination; a guarantee `G(x, [A, B])` is an amount and an ordered
    list of destinations; `item.amount = x` in both cases. S2:742-743 has
    only the allocation form. -/
inductive Item
  | alloc (amount : Coins)
  | guarantee (amount : Coins) (peers : List Address)
  deriving DecidableEq, Repr

/-- S3:324-325 `item.amount`. -/
def Item.amount : Item → Coins
  | .alloc a => a
  | .guarantee x _ => x

/-- S3:352 `isGuarantee`. -/
def Item.isGuarantee : Item → Bool
  | .alloc _ => false
  | .guarantee _ _ => true

/-- One entry of an allocation. S2:742-743 "pairs of addresses and totals,
    `(a1:v1, ..., am:vm)`"; S3:334-335 "mapping a destination to either an
    allocation or a guarantee". -/
structure Entry where
  dest : Address
  item : Item
  deriving DecidableEq, Repr

/-- S2:742 total of an entry. -/
def Entry.amount (e : Entry) : Coins := e.item.amount

/-- An allocation. S2:747-749: "The allocation is in priority order".
    S3:339-341: "Keys are ordered from left to right". The list order is the
    priority order. -/
abbrev Allocation := List Entry

/-- S2:744-746: "each address only appears once in the allocation and require
    that implementations enforce this by ignoring any additional entries for a
    given address after the first." This keeps the first entry per address.
    `seen` holds the destinations already kept. -/
def Allocation.dedupFrom (seen : List Address) : Allocation → Allocation
  | [] => []
  | e :: rest =>
    if e.dest ∈ seen then Allocation.dedupFrom seen rest
    else e :: Allocation.dedupFrom (e.dest :: seen) rest

/-- `dedupFrom` with nothing seen. -/
def Allocation.dedup (o : Allocation) : Allocation := Allocation.dedupFrom [] o

/-- The first entry for a destination. -/
def Allocation.find (o : Allocation) (d : Address) : Option Entry :=
  o.find? (fun e => decide (e.dest = d))

/-- S2:770 "the amount owed to B in the outcome of A": the amount of the
    first entry for `d`, or zero. -/
def Allocation.owed (o : Allocation) (d : Address) : Coins :=
  ((o.find d).map Entry.amount).getD 0

/-- S2:742-743: the total due under an allocation. -/
def Allocation.total (o : Allocation) : Coins :=
  (o.map Entry.amount).sum

/-- S2:747-749, S1:1837-1853: pay `held` coins through the entries in
    priority order. Each entry gets `min(owed, remaining)`. Returns the list
    of `(destination, paid)` in entry order. -/
def Allocation.payout : Coins → Allocation → List (Address × Coins)
  | _, [] => []
  | held, e :: rest =>
    let x := min e.amount held
    (e.dest, x) :: Allocation.payout (held - x) rest

/-- What `d` receives when `held` coins are paid out in priority order
    (duplicates after the first entry are ignored, S2:744-746). -/
def Allocation.paidTo (held : Coins) (o : Allocation) (d : Address) : Coins :=
  (((o.dedup.payout held).filter (fun p => decide (p.1 = d))).map (·.2)).sum

/-- S2:749-751: "'A can afford x for B', if B would receive at least x coins,
    were the coins currently held by A to be paid out in priority order." -/
def Allocation.Affords (held : Coins) (o : Allocation) (d : Address) (x : Coins) : Prop :=
  x ≤ o.paidTo held d

instance (held : Coins) (o : Allocation) (d : Address) (x : Coins) :
    Decidable (o.Affords held d x) :=
  inferInstanceAs (Decidable (x ≤ o.paidTo held d))

/-- S2:770, S2:1144: reduce the amount owed to `d` by `x`. Only the first
    entry for `d` changes. -/
def Allocation.reduceOwed (o : Allocation) (d : Address) (x : Coins) : Allocation :=
  match o with
  | [] => []
  | e :: rest =>
    if e.dest = d then
      { e with item := .alloc (e.amount - x) } :: rest
    else
      e :: Allocation.reduceOwed rest d x

/-- S3:358-359 `o_ledger[left] += o_target[0]`: raise the amount of the
    first entry for `d` by `x`. If `d` has no entry, an entry `A(x)` is
    appended at the end (lowest priority). S3 does not say what `+=` does on
    a missing key; append is the modelling choice. -/
def Allocation.addTo (o : Allocation) (d : Address) (x : Coins) : Allocation :=
  match o with
  | [] => [⟨d, .alloc x⟩]
  | e :: rest =>
    if e.dest = d then
      { e with item := .alloc (e.amount + x) } :: rest
    else
      e :: Allocation.addTo rest d x

/-- S3:361 `delete o_ledger[targetChannelId]`. -/
def Allocation.remove (o : Allocation) (d : Address) : Allocation :=
  o.filter (fun e => decide (e.dest ≠ d))

/-- S3:340-341 `o[i]`: the amount at index `i`, or zero. -/
def Allocation.amountAt (o : Allocation) (i : Nat) : Coins :=
  ((o[i]?).map Entry.amount).getD 0

/-- S2:1098-1101: "the guarantee provides a list of addresses, with the rule
    that these addresses will be moved to the top of the priority order if
    they appear in the outcome." Example: guarantee `(L|A, B, C)` and outcome
    `(C:1, D:2, A:4)` pay as `(A:4, C:1, D:2)`. -/
def Allocation.reprioritize (priority : List Address) (o : Allocation) : Allocation :=
  priority.filterMap o.find ++ o.filter (fun e => decide (e.dest ∉ priority))

/-- The outcome of a channel. S2:1051-1052: "the outcome of a channel can be
    either an allocation or a guarantee." S2:1071-1072: "A guarantee targets
    an allocation, while specifying a different priority order to pay out to
    the destinations." S1:644-665 has only the allocation form (`Uint[]`
    indexed by participant). -/
inductive Outcome
  | allocation (entries : Allocation)
  | guarantee (target : Address) (priority : List Address)
  deriving DecidableEq, Repr

/-- The allocation of an allocation outcome. -/
def Outcome.allocation? : Outcome → Option Allocation
  | .allocation o => some o
  | .guarantee _ _ => none

/-- S2:1109-1111: "'G can afford x for B', if B would receive at least x
    coins, were the coins currently held by G to be paid out according to G's
    prioritization of its target." `target` is the target's allocation. -/
def GuaranteeAffords (held : Coins) (priority : List Address) (target : Allocation)
    (d : Address) (x : Coins) : Prop :=
  (target.reprioritize priority).Affords held d x

instance (held : Coins) (priority : List Address) (target : Allocation) (d : Address)
    (x : Coins) : Decidable (GuaranteeAffords held priority target d x) :=
  inferInstanceAs (Decidable ((target.reprioritize priority).Affords held d x))

/-- S2:1140 "G acts as guarantee for L". -/
def Outcome.guarantees (g : Outcome) (l : Address) : Prop :=
  ∃ priority, g = .guarantee l priority

end ArmadaLean.Nitro
