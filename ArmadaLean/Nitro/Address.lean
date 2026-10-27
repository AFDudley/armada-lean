/-
  Nitro protocol specification: addresses, coins, balances.

  Sources, in the order of `docs/lean/writing-lean.md` "Source order": the
  latest paper first, then the code.
  - SATP: Stewart et al. 2022, `armada-laconic/.scratch/rewrite-B/satp-2022.txt`
  - Nitro: Close 2019, `nitro-2019-219.txt`
  - ForceMove: Close and Stewart 2018, `forcemove-2018.txt`
  - go-nitro: `statechannels/go-nitro` at `64c4ee9a1`,
    `packages/nitro-protocol/contracts/` (last contract change `9d3a669e5`)
  - docs: the docs.statechannels.org tutorial (property ids `docs-*` only)
  Line numbers are in the pdftotext files. The mapping from property ids to
  declarations is in `docs/nitro-theorems.md`.

  Modelling choice (single asset). SATP and go-nitro handle many assets
  (go-nitro `holdings[asset][channelId]`, MultiAssetHolder.sol:23). Nitro:142-148
  treats one asset, "coins". This specification is one single-asset instance.
  No operation in SATP, Nitro or go-nitro moves value between assets, so a
  multi-asset adjudicator is a family of independent instances.
-/

namespace ArmadaLean.Nitro

/-- Coins. Nitro:142-145: "quantities of coins will have no maximum size,
    taking values in `Z+`". go-nitro uses `uint256` amounts; the bound is an
    encoding and is not modelled. -/
abbrev Coins := Nat

/-- Chain time. SATP:297 compares the finalization time with `now`;
    go-nitro StatusManager.sol:8-9 compares it with `block.timestamp`. -/
abbrev Time := Nat

/-- A participant. SATP:199 `peers : PublicKey[]`; Nitro:154-155: "A
    participant address is a regular blockchain address". The key is an
    opaque label. No arithmetic is done on it. -/
structure Participant where
  key : Nat
  deriving DecidableEq, Repr

/-- An application definition. SATP:200 `appDef : Address`; go-nitro
    INitroTypes.sol:16 `appDefinition`. The label is opaque. -/
structure AppId where
  id : Nat
  deriving DecidableEq, Repr

/-- The fixed part of a channel. SATP:198-203 `ChannelConsts { peers, appDef,
    nonce, challengeDuration }`; go-nitro INitroTypes.sol:13-18 `FixedPart
    { participants, channelNonce, appDefinition, challengeDuration }`. The
    two agree. -/
structure FixedPart where
  participants : List Participant
  nonce : Nat
  appDef : AppId
  challengeDuration : Time
  deriving DecidableEq, Repr

/-- The number of participants. ForceMove:607 `numberOfParticipants`;
    go-nitro ForceMove.sol `fixedPart.participants.length`. -/
def FixedPart.n (c : FixedPart) : Nat := c.participants.length

/-- An outcome destination. Operator ruling 2026-10-27: a destination is a
    channel or an external destination, and the type `E` of external
    destinations is a parameter of the specification. SATP:320-321 and
    SATP:334-335: "an outcome is an ordered dictionary, mapping a destination
    to either an allocation or a guarantee". go-nitro: a destination is a
    channel id or an external destination (MultiAssetHolder.sol:436
    `_isExternalDestination`). Nitro:152-157 calls the external kind a
    "participant address"; the signers of a channel are a separate list,
    `FixedPart.participants`, and are not destinations. A channel address is
    the constructor `channel` applied to the fixed part, so two fixed parts
    with different fields give different addresses by construction
    (SATP:213, Nitro:158-160). -/
inductive Address (E : Type)
  | external (e : E)
  | channel (c : FixedPart)
  deriving DecidableEq, Repr

variable {E : Type}

/-- The channel id. SATP:213: "computed from its constants as hash(peers,
    appDef, nonce)". go-nitro NitroUtils.sol:122-133 hashes all four fields,
    with `challengeDuration`. The model follows the code: the id is the whole
    fixed part. -/
def FixedPart.address (c : FixedPart) : Address E := .channel c

/-- go-nitro MultiAssetHolder.sol:436 `_isExternalDestination`. -/
def Address.isExternal : Address E → Bool
  | .external _ => true
  | .channel _ => false

/-- A balance table. Nitro:161-163: "a simple mapping that stores the
    quantity of coins for an address. If an address does not appear in the
    table we take the balance to be zero." go-nitro MultiAssetHolder.sol:23
    `holdings` stores a balance per channel id only. In this model a channel
    entry is the coins the adjudicator holds for the channel; an external
    entry is the coins the adjudicator paid out to that destination (go-nitro
    `_executeSingleAssetExit`, MultiAssetHolder.sol:402-415). -/
abbrev Balances (E : Type) := List (Address E × Coins)

variable [DecidableEq E]

/-- Nitro:162-163: an absent address reads as zero. -/
def Balances.get (b : Balances E) (a : Address E) : Coins :=
  (b.lookup a).getD 0

/-- Write one address. The old entries for that address are dropped, so each
    address has one entry. -/
def Balances.set (b : Balances E) (a : Address E) (v : Coins) : Balances E :=
  (a, v) :: b.filter (fun e => decide (e.1 ≠ a))

/-- Raise a balance by `x`. -/
def Balances.add (b : Balances E) (a : Address E) (x : Coins) : Balances E :=
  b.set a (b.get a + x)

/-- Lower a balance by `x`. -/
def Balances.sub (b : Balances E) (a : Address E) (x : Coins) : Balances E :=
  b.set a (b.get a - x)

/-- Nitro:230-231: "the sum of the balances". -/
def Balances.total (b : Balances E) : Coins :=
  (b.map (·.2)).sum

/-- The sum of the channel balances: the coins the adjudicator holds
    (go-nitro `holdings`). -/
def Balances.channelTotal (b : Balances E) : Coins :=
  ((b.filter (fun e => decide (e.1.isExternal = false))).map (·.2)).sum

/-- The sum of the external balances: the coins the adjudicator paid out. -/
def Balances.paidOutTotal (b : Balances E) : Coins :=
  ((b.filter (fun e => decide (e.1.isExternal = true))).map (·.2)).sum

end ArmadaLean.Nitro
