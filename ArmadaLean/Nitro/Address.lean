/-
  Nitro protocol specification: addresses, coins, balances.

  Sources (line numbers are in the pdftotext files under
  `armada-laconic/.scratch/rewrite-B/`):
  - S1 `forcemove-2018.txt`
  - S2 `nitro-2019-219.txt`
  - S3 `satp-2022.txt`
  The mapping from paper property ids to declarations is in
  `docs/nitro-theorems.md`.

  Modelling choice (single asset). S2:142-148 treats one asset, "coins",
  with values in `Z+` and no maximum. S3 and S4 handle many assets. This
  specification is one single-asset instance. A multi-asset adjudicator is a
  family of independent instances, one per asset, because no operation in
  S1-S3 moves value between assets.
-/

namespace ArmadaLean.Nitro

/-- Coins. S2:142-145: "quantities of coins will have no maximum size, taking
    values in `Z+`". -/
abbrev Coins := Nat

/-- Chain time. S1:1294-1296 compares `endTime` with `now()`; S3:297 compares
    `finalizesAt` with `now`. -/
abbrev Time := Nat

/-- A participant. S2:154-155: "A participant address is a regular blockchain
    address, generated in the standard way from the signature scheme." The key
    is an opaque label. No arithmetic is done on it. -/
structure Participant where
  key : Nat
  deriving DecidableEq, Repr

/-- An application definition. S1:600-602 `channelType`; S3:200 `appDef`.
    The label is opaque. -/
structure AppId where
  id : Nat
  deriving DecidableEq, Repr

/-- The fixed part of a channel. S3:198-203 `ChannelConsts { peers, appDef,
    nonce, challengeDuration }`. S1:600-605 has `channelType, participants,
    channelNonce`. S2:155-157 has the participant addresses and a nonce `k`.
    S3 is the superset, so this is the fixed part. -/
structure FixedPart where
  participants : List Participant
  nonce : Nat
  appDef : AppId
  challengeDuration : Time
  deriving DecidableEq, Repr

/-- S1:606-607 `numberOfParticipants c = c.participants.length`. -/
def FixedPart.n (c : FixedPart) : Nat := c.participants.length

/-- An address. S2:152-157: "Addresses can correspond either to participants
    in the network or to state channels... A channel address is formed by
    taking the hash of the participant addresses along with a nonce". The
    hash is symbolic: the constructor `channel` applied to the fixed part. Two
    fixed parts with different fields give different addresses by
    construction (S2:158-160, S1:610-632, S3:213). -/
inductive Address
  | participant (p : Participant)
  | channel (c : FixedPart)
  deriving DecidableEq, Repr

/-- S2:155-157, S3:213: the channel id is the hash of the constants. -/
def FixedPart.address (c : FixedPart) : Address := .channel c

/-- S2:227-229: "funds can only be withdrawn from participant addresses". -/
def Address.isParticipant : Address → Bool
  | .participant _ => true
  | .channel _ => false

/-- The adjudicator's balance table. S2:161-163: "a simple mapping that stores
    the quantity of coins for an address. If an address does not appear in
    the table we take the balance to be zero." -/
abbrev Balances := List (Address × Coins)

/-- S2:162-163: an absent address reads as zero. -/
def Balances.get (b : Balances) (a : Address) : Coins :=
  (b.lookup a).getD 0

/-- Write one address. The old entries for that address are dropped, so each
    address has one entry. -/
def Balances.set (b : Balances) (a : Address) (v : Coins) : Balances :=
  (a, v) :: b.filter (fun e => decide (e.1 ≠ a))

/-- S2:165-166: raise a balance by `x`. -/
def Balances.add (b : Balances) (a : Address) (x : Coins) : Balances :=
  b.set a (b.get a + x)

/-- S2:169-170: lower a balance by `x`. -/
def Balances.sub (b : Balances) (a : Address) (x : Coins) : Balances :=
  b.set a (b.get a - x)

/-- S2:230-231: "the sum of the balances". -/
def Balances.total (b : Balances) : Coins :=
  (b.map (·.2)).sum

end ArmadaLean.Nitro
