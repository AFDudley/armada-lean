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

/-- An address. Nitro:152-157: "Addresses can correspond either to
    participants in the network or to state channels... A channel address is
    formed by taking the hash of the participant addresses along with a
    nonce". go-nitro: a destination is a channel id or an external address
    (MultiAssetHolder.sol `_isExternalDestination`). SATP is silent on
    participant destinations. The hash is symbolic: the constructor `channel`
    applied to the fixed part. Two fixed parts with different fields give
    different addresses by construction (SATP:213, Nitro:158-160). -/
inductive Address
  | participant (p : Participant)
  | channel (c : FixedPart)
  deriving DecidableEq, Repr

/-- The channel id. SATP:213: "computed from its constants as hash(peers,
    appDef, nonce)". go-nitro NitroUtils.sol:122-133 hashes all four fields,
    with `challengeDuration`. The model follows the code: the id is the whole
    fixed part. -/
def FixedPart.address (c : FixedPart) : Address := .channel c

/-- go-nitro MultiAssetHolder.sol `_isExternalDestination`: a participant
    address is an external destination. -/
def Address.isParticipant : Address → Bool
  | .participant _ => true
  | .channel _ => false

/-- A balance table. Nitro:161-163: "a simple mapping that stores the
    quantity of coins for an address. If an address does not appear in the
    table we take the balance to be zero." go-nitro MultiAssetHolder.sol:23
    `holdings` stores a balance per channel id only. In this model a channel
    entry is the coins the adjudicator holds for the channel; a participant
    entry is the coins the adjudicator paid out to the participant (go-nitro
    `_executeSingleAssetExit`, MultiAssetHolder.sol:396-408). -/
abbrev Balances := List (Address × Coins)

/-- Nitro:162-163: an absent address reads as zero. -/
def Balances.get (b : Balances) (a : Address) : Coins :=
  (b.lookup a).getD 0

/-- Write one address. The old entries for that address are dropped, so each
    address has one entry. -/
def Balances.set (b : Balances) (a : Address) (v : Coins) : Balances :=
  (a, v) :: b.filter (fun e => decide (e.1 ≠ a))

/-- Raise a balance by `x`. -/
def Balances.add (b : Balances) (a : Address) (x : Coins) : Balances :=
  b.set a (b.get a + x)

/-- Lower a balance by `x`. -/
def Balances.sub (b : Balances) (a : Address) (x : Coins) : Balances :=
  b.set a (b.get a - x)

/-- Nitro:230-231: "the sum of the balances". -/
def Balances.total (b : Balances) : Coins :=
  (b.map (·.2)).sum

/-- The sum of the channel balances: the coins the adjudicator holds
    (go-nitro `holdings`). -/
def Balances.channelTotal (b : Balances) : Coins :=
  ((b.filter (fun e => decide (e.1.isParticipant = false))).map (·.2)).sum

/-- The sum of the participant balances: the coins the adjudicator paid out. -/
def Balances.paidOutTotal (b : Balances) : Coins :=
  ((b.filter (fun e => decide (e.1.isParticipant = true))).map (·.2)).sum

end ArmadaLean.Nitro
