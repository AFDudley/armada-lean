/-
  ArmadaLean.Adjudicator.Outcome — the outcome: allocations, guarantees, and
  the priority payout rule.

  This file holds the state and math for "what an outcome pays, and to
  whom". Each definition below carries the exact source quote it translates.
  Sources: S1 ForceMove (Close, Stewart, 2018), S2 Nitro Protocol (Close,
  2019), S3 SATP (Stewart et al., 2022), S4 docs.statechannels.org protocol
  tutorial pages (live site, retrieved 2026-10-18; local copies under
  `armada-nitro/docs/references/nitro/sources/`). This module holds the
  OUTCOME pieces; `Channel.lean` holds the state, signature and
  finalizability pieces that use them.
-/
import ArmadaLean.ValueConservation
import ArmadaLean.Poseidon

namespace ArmadaLean.Adjudicator

/-!
## Allocation type

S4 `0030-outcomes.md` ("Allocations"): "An `allocation` is a `destination`
and an `amount`... an `allocationType` identifier... The `allocationType`
identifier is usually set to 0, meaning 'simple'." And ("Guarantees"):
"When `allocationType` is set to `guarantee`, funds cannot be transferred
in the usual way. Instead, they may be moved to another channel on chain
using the `reclaim` method."

S2 §6.1 calls the same two shapes `A(a)` (an allocation of amount `a`) and
`G(x, [A, B])` (a guarantee of amount `x` reprioritizing `[A, B]`).

The Armada layer adds a third tag, `shield`: a payout that mints a fresh
pool note instead of paying an external account directly
(`ArmadaNitroAdjudicator.sol:18`, `SHIELD_ALLOCATION_TYPE`). No paper
names this tag; it exists only because this adjudicator's money is
pool notes, not a raw balance (see `Notes.lean`).
-/
inductive AllocationType where
  | simple
  | guarantee
  | shield
  deriving DecidableEq

/-- A plain-number tag for each `AllocationType`, used only to fold an
    allocation's type into its `Term` encoding (`Allocation.toTerm`
    below) — Lean bookkeeping, not a protocol concept. Injective by a
    direct case split (`AllocationType.toNat_inj`). -/
def AllocationType.toNat : AllocationType → Nat
  | .simple => 0
  | .guarantee => 1
  | .shield => 2

theorem AllocationType.toNat_inj {a b : AllocationType} (h : a.toNat = b.toNat) : a = b := by
  cases a <;> cases b <;> simp_all [AllocationType.toNat]

/-- An allocation (S4 `0030-outcomes.md`, "Allocations"; S2 §6.1's `A(a)`).
    `destination` and `amount` are the quoted fields; `allocationType`
    distinguishes `simple` from `guarantee`; `metadata` is the quoted
    "optional `metadata`" field, read by a guarantee allocation
    (`decodeGuarantee` below) and otherwise unused. `destination` is a
    `Term`: S4 `0030-outcomes.md`'s "Destinations" names it a `bytes32`
    that either denotes a channel id (`channelId`, `Channel.lean` — a
    genuine keccak256 output, a `Term.hash` term) or an external address
    left-padded with zeros (a raw value, `Term.val` — `isExternal`
    below). -/
structure Allocation where
  destination : Term
  amount : Nat
  allocationType : AllocationType
  metadata : Nat
  deriving DecidableEq

/-- The default allocation, used only to discharge an index lookup already
    proven in range; its fields are never read in that case. Not a paper
    concept — a Lean bookkeeping device. -/
def Allocation.default : Allocation := ⟨Term.val 0, 0, .simple, 0⟩

/-- An allocation's `Term` encoding, for folding into an outcome's hash
    (`SingleAssetExit.toTerm`/`Outcome.toTerm` below). Injective
    (`Allocation.toTerm_inj`) by `Term.hash`'s own constructor
    injectivity, applied to this 4-field tuple. -/
def Allocation.toTerm (a : Allocation) : Term :=
  Term.hash [a.destination, Term.val a.amount, Term.val a.allocationType.toNat, Term.val a.metadata]

/-- If `f` is injective, mapping it over a list is injective. Core/Std
    carries no such lemma (it is a mathlib fact, `List.map_injective_iff`,
    and this repo has no mathlib dependency), so it is proved here, by
    structural induction on both lists together. -/
theorem List.map_injective_of_injective {α β : Type} {f : α → β}
    (hf : ∀ a b, f a = f b → a = b) :
    ∀ l1 l2 : List α, l1.map f = l2.map f → l1 = l2
  | [], [] => fun _ => rfl
  | [], _ :: _ => fun h => by simp at h
  | _ :: _, [] => fun h => by simp at h
  | a :: as, b :: bs => fun h => by
    simp only [List.map_cons, List.cons.injEq] at h
    obtain ⟨h1, h2⟩ := h
    rw [hf a b h1, List.map_injective_of_injective hf as bs h2]

theorem Allocation.toTerm_inj {a b : Allocation} (h : a.toTerm = b.toTerm) : a = b := by
  unfold Allocation.toTerm at h
  injection h with hl
  simp only [List.cons.injEq] at hl
  obtain ⟨h1, h2, h3, h4⟩ := hl
  have ha := Term.val.inj h2
  have ht := AllocationType.toNat_inj (Term.val.inj h3)
  have hm := Term.val.inj h4.1
  cases a; cases b
  simp_all


/-- A single asset's exit (S4 `0030-outcomes.md`: "An `Outcome` is an array
    of `SingleAssetExits`, each specifying: an `asset`; optional
    `assetMetadata`; an ordered list of `allocations`."). `assetMetadata` is
    elided: the quote itself says it "is used only by more exotic asset
    types, and is zero-ed out for native and ERC20 assets" — the only two
    kinds this adjudicator and its pool handle (`TokenType.ERC20`,
    `IArmadaPool.sol:8-12`), so it carries no case this model needs to
    distinguish. -/
structure SingleAssetExit where
  asset : Nat
  allocations : List Allocation

/-- A single-asset-exit's `Term` encoding, for folding into an outcome's
    hash (`Outcome.toTerm` below). Injective (`SingleAssetExit.toTerm_inj`)
    by `Term.hash`'s own constructor injectivity plus map-injectivity
    (`List.map_injective_of_injective`, above) lifted from
    `Allocation.toTerm_inj`. -/
def SingleAssetExit.toTerm (e : SingleAssetExit) : Term :=
  Term.hash (Term.val e.asset :: e.allocations.map Allocation.toTerm)

/-- A single-asset-exit's `Term` encoding is injective. -/
theorem SingleAssetExit.toTerm_inj {e1 e2 : SingleAssetExit} (h : e1.toTerm = e2.toTerm) :
    e1 = e2 := by
  unfold SingleAssetExit.toTerm at h
  injection h with hl
  simp only [List.cons.injEq] at hl
  obtain ⟨ha, hallocs⟩ := hl
  have ha' := Term.val.inj ha
  have hallocs' := List.map_injective_of_injective
    (fun a b => Allocation.toTerm_inj) e1.allocations e2.allocations hallocs
  cases e1; cases e2
  simp_all

/-- A channel's outcome (S4 `0010-states-channels.md`, `VariablePart.outcome
: Outcome.SingleAssetExit[]`; S2 §3.2, "An outcome dictates how assets...
will be redistributed"). S2 §3.2 also states the outcome is "an ordered
dictionary, mapping a destination to either an allocation or a guarantee" —
S4's array-of-`SingleAssetExit`s is the asset-indexed version of the same
idea; S2 itself predates multi-asset outcomes (S2 §3.1 restricts to "a
single asset, which we will refer to as coins"). -/
abbrev Outcome := List SingleAssetExit

/-- An outcome's `Term` encoding (`Assumptions.lean`'s `outcomeHashOf`).
    Injective (`Outcome.toTerm_inj`), the same proof shape as
    `SingleAssetExit.toTerm_inj` one layer up. -/
def Outcome.toTerm (o : Outcome) : Term := Term.hash (o.map SingleAssetExit.toTerm)

theorem Outcome.toTerm_inj {o1 o2 : Outcome} (h : o1.toTerm = o2.toTerm) : o1 = o2 := by
  unfold Outcome.toTerm at h
  injection h with hl
  exact List.map_injective_of_injective (fun a b => SingleAssetExit.toTerm_inj) o1 o2 hl

/-- A destination is external when its top 96 bits are zero (S4
    `0030-outcomes.md`, "Destinations": "A `destination` is [a] 32 byte
    identifier which may either denote a channel ID or a so-called
    'external destination' (a 20 byte Ethereum address left-padded with
    zeros)."). `destination` is a `Term` now (`Allocation.destination`'s
    own doc comment): an external destination is a RAW value (an address,
    embedded `Term.val`), never a genuine hash — a channel id
    (`Channel.lean`'s `channelId`) is always a `Term.hash` term, so
    `Term.val_ne_hash` already rules out a channel id ever being
    external, with no separate numeric check needed for that direction. -/
def isExternal (destination : Term) : Prop := ∃ a : Nat, a < 2 ^ 160 ∧ destination = Term.val a

/-- The priority payout rule (S2 §5.1, "Allocations and Transfer": "The
    allocation is in priority order, so that if the channel does not hold
    enough funds to pay all the coins that are due, then the addresses at
    the beginning of the allocation will receive funds first. We say that
    'A can afford x for B', if B would receive at least x coins, were the
    coins currently held by A to be paid out in priority order." — and the
    Turbo Value Algorithm, S2 §5.2, step 3(b)(i): "Let x = min(payout,
    remainingFunds)."). `afford allocs surplus` returns the amount actually
    paid to each entry of `allocs`, in order, out of `surplus`. -/
def afford : List Allocation → Nat → List Nat
  | [], _ => []
  | a :: as, surplus =>
    let paid := min a.amount surplus
    paid :: afford as (surplus - paid)

/-!
## Selecting which indices `transfer` pays now

`MultiAssetHolder.sol:135-191`, `compute_transfer_effects_and_interactions`:
surplus is consumed in priority order for EVERY allocation, whether or not
its index is selected (`affordsForDestination = min(allocations[i].amount,
surplus)` runs unconditionally inside the loop, `:167`; `surplus -=
affordsForDestination` at `:189` runs every iteration too). Only a
SELECTED allocation (`indices[k] == i`, or every index when `indices` is
empty, `:149,168`) is actually paid now and has its recorded amount
reduced (`:173-181`); an unselected allocation keeps its full recorded
amount (`:185`) even though the priority pass already "spent" surplus
computing what it would have received. `indices == []` means "pay out to
all" (`:149`, the exact words of the code comment).
-/

/-- `MultiAssetHolder._requireIncreasingIndices` (`:528-535`): "Checks that
    the supplied indices are strictly increasing. This allows us... to
    write a more efficient claim function." -/
def StrictlyIncreasing : List Nat → Prop
  | [] => True
  | [_] => True
  | a :: b :: rest => a < b ∧ StrictlyIncreasing (b :: rest)

/-- `compute_transfer_effects_and_interactions` (`MultiAssetHolder.sol:
    135-191`, quoted above): `transferEffects allocations surplus indices`
    returns `(newAllocations, exitAllocations, totalPayouts)`. Every
    position's priority-order affordable amount (`afford`) is computed
    first; a selected position's allocation is reduced by that amount and
    its paid amount goes to `exitAllocations` (`:173-181`); an unselected
    position's allocation is left at its full recorded amount (`:185`). -/
def transferEffects (allocations : List Allocation) (surplus : Nat) (indices : List Nat) :
    List Allocation × List Allocation × Nat :=
  let paidAt := afford allocations surplus
  let selected (i : Nat) : Bool := indices.isEmpty || i ∈ indices
  let indexed := (List.range allocations.length).zip (allocations.zip paidAt)
  let newAllocations := indexed.map fun (i, a, paid) =>
    if selected i then { a with amount := a.amount - paid } else a
  let exitAllocations := indexed.filterMap fun (i, a, paid) =>
    if selected i then some { a with amount := paid } else none
  (newAllocations, exitAllocations, listSum (exitAllocations.map Allocation.amount))

/-!
## Guarantees

S4 `0030-outcomes.md`, "Guarantees": "The `metadata` is an encoding of the
following struct: `struct Guarantee { bytes32 left; bytes32 right; }` where
`left` and `right` correspond to channel participants." S2 §6.1 is the same
shape under a different name: "A guarantee is a data structure G(x,[A,B])
representing an amount x and an ordered list of destinations A and B."

A gap between S2 and S4/the code: S2 §6.1 generalizes a guarantee's target
list to any length ("the guarantee provides a list of addresses"), ranked
by priority, matching the outcome they target. S4 and the vendored code fix
the list at exactly two entries, `{left, right}`
(`MultiAssetHolder.sol:538-545`). `clauses.md` records the same gap as
Sil6: "S3 Listing 2 and S4 `0080` describe reclaim for a two-party target.
The code credits only `targetAllocations[0]` and `[1]`." This model follows
S4/S3/the code (two destinations), not S2's general list, because the code
this model checks (`PoolSpend.settleReclaim`, see `Notes.lean`) only ever
reclaims a two-party guarantee.
-/

/-- A guarantee's metadata decodes to its two reprioritized destinations
    (S4 `0030-outcomes.md`, quoted above). Modeled as an abstract decoder:
    the encode/decode round trip carries no content this model needs beyond
    "it recovers the two addresses the guarantee's creator encoded". -/
axiom decodeGuarantee : Nat → Term × Term

/-- Credits `amt` to the FIRST allocation in `allocs` whose own
    `destination` equals `dest`, leaving every other entry UNCHANGED —
    `MultiAssetHolder.sol:341-390`'s `compute_reclaim_effects`
    (`src/nitro`, vendored upstream), the `foundLeft`/`foundRight`-flag
    loop at `:371-380`: each destination is matched AT MOST ONCE, so a
    later allocation that happens to share the same destination is left
    alone. -/
def creditFirst (allocs : List Allocation) (dest : Term) (amt : Nat) : List Allocation :=
  match allocs with
  | [] => []
  | a :: rest =>
    if a.destination = dest then { a with amount := a.amount + amt } :: rest
    else a :: creditFirst rest dest amt

/-- `reclaim`'s effect on the source (ledger) channel's own outcome (S3
    §2.4, Listing 2, "Reclaim": `o_ledger[left] += o_target[0]`;
    `o_ledger[right] += o_target[1]`; `delete o_ledger[targetChannelId]` —
    i.e. drop the guarantee and credit its two reprioritized destinations by
    the target's first two allocation amounts). Each credit lands on the
    FIRST matching allocation only (`creditFirst`, above) — running `left`
    then `right` in sequence reproduces `compute_reclaim_effects`'s own
    SINGLE-PASS `foundLeft`/`foundRight` loop (`MultiAssetHolder.sol:
    371-380`) exactly, INCLUDING `left = right`: the second pass's own
    first match is the SAME entry the first pass already credited, so it
    receives both credits, matching the contract's two separate `if`s on
    one entry. Every other asset's exit, and every other allocation of
    the named asset, is unchanged. -/
def reallocateGuarantee (outcome : Outcome) (assetIndex allocIndex : Nat)
    (left right : Term) (amtLeft amtRight : Nat) : Outcome :=
  outcome.mapIdx fun i exit =>
    if i ≠ assetIndex then exit
    else { exit with
      allocations := creditFirst (creditFirst (exit.allocations.eraseIdx allocIndex) left amtLeft)
        right amtRight }

/-!
## An outcome derived from an earlier one by `transfer`/`reclaim`

Once a channel is finalized, `.transfer` and `.reclaim`
(`Operations.lean`) both go on rewriting that channel's OWN
`outcomeHash`, holding its `stateHash` fixed — a `.transfer` call
reduces one asset's allocations by `transferEffects`'s own
`newAllocations`, and a `.reclaim` call replaces an asset's allocations
via `reallocateGuarantee`. `OutcomeDerivedFrom o o'` says `o'` is `o`,
or some chain of these two kinds of rewrite away from it —
`finalized_outcome_was_concluded_or_challenged` (`Safety.lean`) needs
this to state that a finalized channel's CURRENT outcome need not be
the signed/challenged outcome ITSELF, only derived from it this way.
-/
inductive OutcomeDerivedFrom : Outcome → Outcome → Prop where
  | refl (o : Outcome) : OutcomeDerivedFrom o o
  /-- `transferEffects`'s `newAllocations` (`.1`) only ever REDUCES a
      SELECTED allocation's own amount, by `afford`'s own paid amount
      (`afford_le`, `Lemmas.lean`: `paid ≤ a.amount`) — never increases
      one, never changes a destination, asset, or allocation type, and
      never touches an UNSELECTED position at all. So an adversarially
      chosen `heldBefore` (this `.transfer` call's own claimed
      `heldValue`) can only make this step pay out LESS, never credit a
      destination it did not already hold — safe to leave free here. -/
  | transferStep {o mid : Outcome} (assetIndex : Nat) (h : assetIndex < mid.length)
      (heldBefore : Nat) (indices : List Nat) (hmid : OutcomeDerivedFrom o mid) :
      OutcomeDerivedFrom o
        (mid.mapIdx fun i exit => if i ≠ assetIndex then exit else
          { exit with allocations :=
              (transferEffects (mid.get ⟨assetIndex, h⟩).allocations heldBefore indices).1 })
  /-- Mirrors `.reclaim`'s OWN preconditions (`Operations.lean`) exactly,
      not a free rewrite: `allocIndex` must name a `.guarantee`
      allocation (`guarantee.allocationType = .guarantee`); the credited
      destinations are `decodeGuarantee`'s OWN output on that
      guarantee's OWN metadata, not independently chosen; the two
      credited amounts must SUM TO EXACTLY the guarantee's own amount
      (`a0 + a1 = guarantee.amount`, `Operations.lean`'s `.reclaim`
      case); and EACH destination must match some OTHER allocation
      already in the list, matching `compute_reclaim_effects`'s own
      `require(foundLeft)`/`require(foundRight)` (`MultiAssetHolder.sol:
      385-386`) — so this step can only erase a guarantee ALREADY
      present in `mid` and redistribute EXACTLY its own amount to two
      destinations that ALREADY hold an allocation, never an arbitrary
      allocation, an arbitrary destination/amount, or a destination with
      nothing to credit. -/
  | reclaimStep {o mid : Outcome} (assetIndex allocIndex : Nat)
      (h1 : assetIndex < mid.length)
      (h2 : allocIndex < (mid.get ⟨assetIndex, h1⟩).allocations.length)
      (hguarantee : ((mid.get ⟨assetIndex, h1⟩).allocations.get ⟨allocIndex, h2⟩).allocationType =
        .guarantee)
      (amtLeft amtRight : Nat)
      (hsum : amtLeft + amtRight =
        ((mid.get ⟨assetIndex, h1⟩).allocations.get ⟨allocIndex, h2⟩).amount)
      (hfoundLeft : ∃ a ∈ ((mid.get ⟨assetIndex, h1⟩).allocations.eraseIdx allocIndex),
        a.destination = (decodeGuarantee
          ((mid.get ⟨assetIndex, h1⟩).allocations.get ⟨allocIndex, h2⟩).metadata).1)
      (hfoundRight : ∃ a ∈ ((mid.get ⟨assetIndex, h1⟩).allocations.eraseIdx allocIndex),
        a.destination = (decodeGuarantee
          ((mid.get ⟨assetIndex, h1⟩).allocations.get ⟨allocIndex, h2⟩).metadata).2)
      (hmid : OutcomeDerivedFrom o mid) :
      OutcomeDerivedFrom o (reallocateGuarantee mid assetIndex allocIndex
        (decodeGuarantee ((mid.get ⟨assetIndex, h1⟩).allocations.get ⟨allocIndex, h2⟩).metadata).1
        (decodeGuarantee ((mid.get ⟨assetIndex, h1⟩).allocations.get ⟨allocIndex, h2⟩).metadata).2
        amtLeft amtRight)

/-- `OutcomeDerivedFrom` is unaffected by a FIXED head entry: if `rest` is
    derived into `newRest`, prepending the SAME `head` to both sides is
    still a valid derivation — each step just moves one index further
    into the list (`List.mapIdx_cons`). What `bulkTransferFold_outcomeDerivedFrom`
    (`Lemmas.lean`) needs to chain its own per-asset rewrites, one list
    element at a time, into a single `OutcomeDerivedFrom` fact. -/
theorem OutcomeDerivedFrom_cons (head : SingleAssetExit) {rest newRest : Outcome}
    (h : OutcomeDerivedFrom rest newRest) :
    OutcomeDerivedFrom (head :: rest) (head :: newRest) := by
  induction h with
  | refl => exact OutcomeDerivedFrom.refl (head :: rest)
  | @transferStep mid assetIndex hidx heldBefore indices hmid ih =>
    have hidx' : assetIndex + 1 < (head :: mid).length := by simpa using hidx
    have hstep := OutcomeDerivedFrom.transferStep (o := head :: rest) (assetIndex + 1) hidx'
      heldBefore indices ih
    rw [List.mapIdx_cons] at hstep
    simpa [List.get_cons_succ] using hstep
  | @reclaimStep mid assetIndex allocIndex h1 h2 hguarantee amtLeft amtRight hsum hfoundLeft
      hfoundRight hmid ih =>
    have h1' : assetIndex + 1 < (head :: mid).length := by simpa using h1
    have h2' : allocIndex < ((head :: mid).get ⟨assetIndex + 1, h1'⟩).allocations.length := by
      simpa [List.get_cons_succ] using h2
    have hstep := OutcomeDerivedFrom.reclaimStep (o := head :: rest) (assetIndex + 1) allocIndex h1' h2'
      (by simpa [List.get_cons_succ] using hguarantee) amtLeft amtRight
      (by simpa [List.get_cons_succ] using hsum)
      (by simpa [List.get_cons_succ] using hfoundLeft) (by simpa [List.get_cons_succ] using hfoundRight)
      ih
    unfold reallocateGuarantee at hstep ⊢
    rw [List.mapIdx_cons] at hstep
    simpa [List.get_cons_succ] using hstep

/-- `OutcomeDerivedFrom` is transitive: a chain of rewrites onto a chain
    of rewrites is one longer chain. What the bulk-call cases of
    `finalized_outcome_was_concluded_or_challenged` (`Safety.lean`) need
    to extend an EARLIER derivation (`candidate.outcome` to the channel's
    outcome BEFORE this step) by `bulkTransferFold`'s own derivation
    (that outcome to the one AFTER this step). -/
theorem OutcomeDerivedFrom.trans {o1 o2 o3 : Outcome}
    (h12 : OutcomeDerivedFrom o1 o2) (h23 : OutcomeDerivedFrom o2 o3) :
    OutcomeDerivedFrom o1 o3 := by
  induction h23 with
  | refl => exact h12
  | @transferStep mid assetIndex hidx heldBefore indices hmid ih =>
    exact OutcomeDerivedFrom.transferStep assetIndex hidx heldBefore indices ih
  | @reclaimStep mid assetIndex allocIndex h1 h2 hguarantee amtLeft amtRight hsum hfoundLeft
      hfoundRight hmid ih =>
    exact OutcomeDerivedFrom.reclaimStep assetIndex allocIndex h1 h2 hguarantee amtLeft amtRight
      hsum hfoundLeft hfoundRight ih




end ArmadaLean.Adjudicator
