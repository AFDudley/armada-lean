/-
  ArmadaLean.Adjudicator.Assumptions — two of the three facts no caller can
  change: a hash cannot be inverted or collided, and a signature cannot be
  forged.

  Phase 1 brief (`armada-laconic/.scratch/rewrite-B/PHASE1-lean-model.md`),
  "Why this model exists": "The only things the model takes as given are
  things no caller can change: that the hash cannot be inverted or
  collided, that a signature cannot be forged, and that an accepted proof
  means its constraints hold." This file states the first two, each as a
  named Lean axiom. The third (proof soundness) sits in `Notes.lean`, next
  to the owned-spend circuit it is about.

  The pool layer already states two hash axioms and one signature axiom in
  the root `ArmadaLean` modules (`Poseidon.lean`'s `poseidon2_inj`/
  `poseidon3_inj`, `Transact.lean`'s `EdDSAVerify`). This file does not
  repeat them; it adds the Nitro layer's own instances, because the Nitro
  layer hashes with keccak256 and signs with ECDSA/EIP-1271 — different
  primitives from the pool's Poseidon/EdDSA. Every theorem that uses a hash
  or a signature fact takes the matching axiom below (or the pool's) as an
  explicit hypothesis, never as a hidden fact of the proof.
-/

namespace ArmadaLean.Adjudicator

/-!
## Assumption 1: a hash cannot be inverted or collided (Nitro layer)

S4 `0010-states-channels.md`, "Channel IDs": "Channels are identified by
the hash of the `FixedPart` of the state... `bytes32 channelId =
keccak256(abi.encode(fixedPart.participants, fixedPart.channelNonce,
fixedPart.appDefinition, fixedPart.challengeDuration));`" (clause 3 of
`armada-nitro/docs/references/nitro/clauses.md`).

S4 `0010-states-channels.md`, "State commitments": "To commit to a state, a
hash is formed as follows: `bytes32 stateHash = keccak256(abi.encode(
channelId, variablePart.appData, variablePart.outcome, variablePart.turnNum,
variablePart.isFinal));`" (clause 4).

S4 `0040-lifecycle-of-a-channel.md`, "fingerprint": "The `fingerprint` helps
to uniquely identify the channel's current state, up to hash collisions. It
is computed as: `uint160(uint256(keccak256(abi.encode(stateHash,
outcomeHash))))`" (clause 12).

Nitro-2019-219.pdf §3.1 states the premise these three quotes rely on:
"we assume... the properties of the signature scheme and hashing algorithm
make it impossible to find a private key for A or to construct a channel
whose address is A, if they are not previously known." That premise —
collision resistance — is exactly what the three axioms below state for
each of the three keccak256 uses the quotes name.
-/

/-- `channelId` as an injective function of the `FixedPart` fields (S4
    `0010-states-channels.md`, "Channel IDs", quoted above). -/
axiom channelIdOf : List Nat → Nat → Nat → Nat → Nat

/-- CRYPTOGRAPHIC ASSUMPTION 1 (collision resistance of keccak256,
    `channelId`) — assumed, not proven. A caller cannot name two distinct
    `FixedPart`s with the same `channelId`: Nitro-2019-219.pdf §3.1, "we
    assume... it [is] impossible... to construct a channel whose address is
    A, if [it is] not previously known." -/
axiom channelIdOf_inj :
  ∀ {p₁ p₂ : List Nat} {n₁ n₂ a₁ a₂ d₁ d₂ : Nat},
    channelIdOf p₁ n₁ a₁ d₁ = channelIdOf p₂ n₂ a₂ d₂ →
    p₁ = p₂ ∧ n₁ = n₂ ∧ a₁ = a₂ ∧ d₁ = d₂

/-- `stateHash` as an injective function of `(channelId, appData, outcome,
    turnNum, isFinal)` (S4 `0010-states-channels.md`, "State commitments",
    quoted above). -/
axiom stateHashOf : Nat → Nat → Outcome → Nat → Bool → Nat

/-- CRYPTOGRAPHIC ASSUMPTION 1 (collision resistance of keccak256,
    `stateHash`) — assumed, not proven. A caller cannot present a state
    whose hash collides with a different, better-supported state. -/
axiom stateHashOf_inj :
  ∀ {c₁ c₂ : Nat} {a₁ a₂ : Nat} {o₁ o₂ : Outcome} {t₁ t₂ : Nat} {f₁ f₂ : Bool},
    stateHashOf c₁ a₁ o₁ t₁ f₁ = stateHashOf c₂ a₂ o₂ t₂ f₂ →
    c₁ = c₂ ∧ a₁ = a₂ ∧ o₁ = o₂ ∧ t₁ = t₂ ∧ f₁ = f₂

/-- `outcomeHash` as an injective function of the outcome alone (S4
    `0040-lifecycle-of-a-channel.md`, "fingerprint", quoted above: the
    `outcomeHash` argument to the fingerprint hash is a hash of the outcome
    on its own, separate from `stateHash`). Needed because `transfer` and
    `reclaim` update only the stored outcome hash, leaving `stateHash`
    unchanged (`Operations.lean`'s `transfer`/`reclaim`, following
    `MultiAssetHolder.sol:203-205,409-413`). -/
axiom outcomeHashOf : Outcome → Nat

/-- CRYPTOGRAPHIC ASSUMPTION 1 (collision resistance of keccak256,
    `outcomeHash`) — assumed, not proven. A caller cannot swap in a
    different outcome that hashes to the one already stored for a channel. -/
axiom outcomeHashOf_inj :
  ∀ {o₁ o₂ : Outcome}, outcomeHashOf o₁ = outcomeHashOf o₂ → o₁ = o₂

/-!
## Assumption 2: a signature cannot be forged (Nitro layer)

S4 `0010-states-channels.md`, "State commitments": a state hash "is signed
using a dedicated Ethereum private key... The signature has the... type:
`struct Signature { uint8 v; bytes32 r; bytes32 s; }`."

S4 `0070-finalizing-a-channel.md`, "Call `challenge`": "The challenger
needs to sign this data: `keccak256(abi.encode(challengeStateHash,
'forceMove'))`... This mechanism allows the challenge to be authorized only
by a channel participant."

SATP (sources/satp-2022.pdf) §1.4 states the premise directly, as one of
its two named security assumptions: "(Safety) Forging cryptographic
signatures is infeasible."

The code extends "signed" to "authorized" for a contract participant (the
hub custodian is one): `NitroUtils.isAuthorizedBy`
(`NitroUtils.sol:101-126`) accepts an EIP-1271 acceptance in place of an
ECDSA recovery. No S1-S4 source states this; `clauses.md` D1 records it as
an armada-nitro addition with no upstream spec clause. This model folds
both paths into one relation, `AuthorizedBy`, because the protocol treats
them identically once authorized — the SATP safety premise ("forging... is
infeasible") is exactly the fact this model needs from either path, and an
EIP-1271 "signature" is a contract's own code choosing to accept, which a
caller cannot forge any more than an ECDSA signature.
-/

/-- CRYPTOGRAPHIC ASSUMPTION 2 (ECDSA / EIP-1271 unforgeability) — assumed,
    not proven. `AuthorizedBy p d` holds iff participant `p` (an EOA or a
    contract) itself produced an authorization over digest `d` — an ECDSA
    signature `p`'s key signed, or an EIP-1271 acceptance `p`'s own code
    returned (`NitroUtils.isAuthorizedBy`, `NitroUtils.sol:101-126`; SATP
    §1.4, "Forging cryptographic signatures is infeasible"). Only the
    *validity* direction is needed: a call that recovers or accepts an
    authorization for `p` is constrained to a case where `AuthorizedBy p d`
    already held. -/
axiom AuthorizedBy : Nat → Nat → Prop

end ArmadaLean.Adjudicator
