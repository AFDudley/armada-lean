/-
  Nitro protocol specification: outcomes, allocations, guarantees, and the
  priority-order payout. See `Address.lean` for the source list.

  Guarantee form. SATP:322-323 and go-nitro (ExitFormat
  `AllocationType.guarantee`, MultiAssetHolder.sol:516-519) give a guarantee
  as one item inside an allocation: `G(x, [left, right])`, consumed by
  `reclaim`. Nitro §6.1 (1070-1074) gave a guarantee as the outcome of a
  whole channel, consumed by `claim`. SATP replaced that form (SATP:367-370,
  footnote 11) and go-nitro has no `claim`. Operator ruling 2026-10-27: the
  Nitro guarantee channel, `claim` and the reprioritization rule are not
  modelled. Only the SATP item form is here.
-/
import ArmadaLean.Nitro.Address

namespace ArmadaLean.Nitro

/-- One outcome item. SATP:320-325: an allocation `A(a)` is an amount paid to
    a destination; a guarantee `G(x, [A, B])` is an amount and an ordered
    list of destinations; `item.amount = x` in both cases. go-nitro:
    `Allocation { destination, amount, allocationType, metadata }` with the
    guarantee metadata `{ left, right }` (MultiAssetHolder.sol:516-519). -/
inductive Item
  | alloc (amount : Coins)
  | guarantee (amount : Coins) (peers : List Address)
  deriving DecidableEq, Repr

/-- SATP:324-325 `item.amount`. -/
def Item.amount : Item → Coins
  | .alloc a => a
  | .guarantee x _ => x

/-- SATP:352 `isGuarantee`; go-nitro MultiAssetHolder.sol:276-280. -/
def Item.isGuarantee : Item → Bool
  | .alloc _ => false
  | .guarantee _ _ => true

/-- One entry of an allocation. SATP:334-335: "mapping a destination to
    either an allocation or a guarantee"; Nitro:742-743 "pairs of addresses
    and totals". -/
structure Entry where
  dest : Address
  item : Item
  deriving DecidableEq, Repr

/-- The total of an entry. -/
def Entry.amount (e : Entry) : Coins := e.item.amount

/-- An allocation. SATP:339-341: "Keys are ordered from left to right";
    SATP:377-379 (footnote 9): "the order may also dictate which destinations
    receive priority". Nitro:747-749: "The allocation is in priority order".
    go-nitro MultiAssetHolder.sol:162-191 pays in list order. -/
abbrev Allocation := List Entry

/-- Nitro:744-746: "each address only appears once in the allocation and
    require that implementations enforce this by ignoring any additional
    entries for a given address after the first." SATP is silent. go-nitro
    "Assumes no repeated entries" (MultiAssetHolder.sol:67). The paper form
    is kept: this keeps the first entry per address. `seen` holds the
    destinations already kept. -/
def Allocation.dedupFrom (seen : List Address) : Allocation → Allocation
  | [] => []
  | e :: rest =>
    if e.dest ∈ seen then Allocation.dedupFrom seen rest
    else e :: Allocation.dedupFrom (e.dest :: seen) rest

/-- `dedupFrom` with nothing seen. -/
def Allocation.dedup (o : Allocation) : Allocation := Allocation.dedupFrom [] o

/-- The first entry for a destination. go-nitro `foundLeft`/`foundRight`
    (MultiAssetHolder.sol:349-358) also take the first match. -/
def Allocation.find (o : Allocation) (d : Address) : Option Entry :=
  o.find? (fun e => decide (e.dest = d))

/-- Nitro:770 "the amount owed to B in the outcome of A": the amount of the
    first entry for `d`, or zero. -/
def Allocation.owed (o : Allocation) (d : Address) : Coins :=
  ((o.find d).map Entry.amount).getD 0

/-- The total due under an allocation. -/
def Allocation.total (o : Allocation) : Coins :=
  (o.map Entry.amount).sum

/-- Priority payout. go-nitro `compute_transfer_effects_and_interactions`
    (MultiAssetHolder.sol:162-191): for each entry in order,
    `affordsForDestination = min(amount, surplus)` and `surplus` falls by it.
    Nitro:747-749 and ForceMove:1837-1853 say the same. Returns the list of
    `(destination, paid)` in entry order. -/
def Allocation.payout : Coins → Allocation → List (Address × Coins)
  | _, [] => []
  | held, e :: rest =>
    let x := min e.amount held
    (e.dest, x) :: Allocation.payout (held - x) rest

/-- What `d` receives when `held` coins are paid out in priority order
    (duplicates after the first entry are ignored, Nitro:744-746). -/
def Allocation.paidTo (held : Coins) (o : Allocation) (d : Address) : Coins :=
  (((o.dedup.payout held).filter (fun p => decide (p.1 = d))).map (·.2)).sum

/-- Nitro:749-751: "'A can afford x for B', if B would receive at least x
    coins, were the coins currently held by A to be paid out in priority
    order." SATP and go-nitro have no named notion; go-nitro pays the
    afforded amount itself. -/
def Allocation.Affords (held : Coins) (o : Allocation) (d : Address) (x : Coins) : Prop :=
  x ≤ o.paidTo held d

instance (held : Coins) (o : Allocation) (d : Address) (x : Coins) :
    Decidable (o.Affords held d x) :=
  inferInstanceAs (Decidable (x ≤ o.paidTo held d))

/-- Reduce the amount owed to `d` by `x`. go-nitro MultiAssetHolder.sol:175
    `newAllocations[i].amount = allocations[i].amount - affordsForDestination`;
    Nitro:770. Only the first entry for `d` changes. -/
def Allocation.reduceOwed (o : Allocation) (d : Address) (x : Coins) : Allocation :=
  match o with
  | [] => []
  | e :: rest =>
    if e.dest = d then
      { e with item := .alloc (e.amount - x) } :: rest
    else
      e :: Allocation.reduceOwed rest d x

/-- SATP:358-359 `o_ledger[left] += o_target[0]`; go-nitro
    MultiAssetHolder.sol:349-358 raises the first entry whose destination is
    `left`. When `d` has no entry nothing changes: go-nitro reverts
    ("could not find left", MultiAssetHolder.sol:363-364), and `reclaim`
    requires the entry. -/
def Allocation.addTo (o : Allocation) (d : Address) (x : Coins) : Allocation :=
  match o with
  | [] => []
  | e :: rest =>
    if e.dest = d then
      { e with item := .alloc (e.amount + x) } :: rest
    else
      e :: Allocation.addTo rest d x

/-- SATP:361 `delete o_ledger[targetChannelId]`; go-nitro
    MultiAssetHolder.sol:335-338 skips the guarantee entry. -/
def Allocation.remove (o : Allocation) (d : Address) : Allocation :=
  o.filter (fun e => decide (e.dest ≠ d))

/-- SATP:340-341 `o[i]`; go-nitro `targetAllocations[0]`,
    `targetAllocations[1]`. The amount at index `i`, or zero. -/
def Allocation.amountAt (o : Allocation) (i : Nat) : Coins :=
  ((o[i]?).map Entry.amount).getD 0

/-- The outcome of a channel. SATP:334-335 and go-nitro: an allocation (the
    guarantee form lives inside it as an item). Nitro:1051-1052's guarantee
    outcome is not modelled (operator ruling 2026-10-27; see the module
    comment). The single-constructor inductive keeps the `.allocation o`
    pattern at every use. -/
inductive Outcome
  | allocation (entries : Allocation)
  deriving DecidableEq, Repr

/-- The allocation of an outcome. -/
def Outcome.entries : Outcome → Allocation
  | .allocation o => o

end ArmadaLean.Nitro
