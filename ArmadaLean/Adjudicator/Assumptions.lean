/-
  ArmadaLean.Adjudicator.Assumptions — two of the three facts no caller can
  change: a hash cannot be inverted or collided, and a signature cannot be
  forged.

  Phase 1 brief (`armada-laconic/.scratch/rewrite-B/PHASE1-lean-model.md`),
  "Why this model exists": "The only things the model takes as given are
  things no caller can change: that the hash cannot be inverted or
  collided, that a signature cannot be forged, and that an accepted proof
  means its constraints hold." This file states the first two. The third
  (proof soundness) sits in `Notes.lean`, next to the owned-spend circuit
  it is about, as `ProofAssumptions`.

  Each assumption is a FIELD of a named structure (`HashAssumptions`,
  `SignatureAssumptions`), never a bare global `axiom`. A bare axiom is a
  fact any proof anywhere can invoke without the theorem's own signature
  showing it; a structure a theorem takes as an explicit argument forces
  the dependency onto the type, so a reader sees from the statement alone
  which assumptions it needs (coordinator correction, this session).
  `channelIdOf`, `stateHashOf` and `outcomeHashOf` stay as bare `axiom`
  declarations: each names an uninterpreted FUNCTION with no asserted
  property (the same status as `AppSupports`/`decodeGuarantee`), not a
  security claim — the security claim is their INJECTIVITY, which is a
  `HashAssumptions` field below.

  The pool layer already states two hash axioms and one signature axiom in
  the root `ArmadaLean` modules (`Poseidon.lean`'s `poseidon2_inj`/
  `poseidon3_inj`, `Transact.lean`'s `EdDSAVerify`), which this file does
  not change — they are the pool layer's own convention, outside this
  phase's scope, and this phase does not touch their proofs. This file adds
  only the Nitro layer's own instances, because the Nitro layer hashes with
  keccak256 and signs with ECDSA/EIP-1271 — different primitives from the
  pool's Poseidon/EdDSA.
-/
import ArmadaLean.Adjudicator.Outcome

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
collision resistance — is exactly what `HashAssumptions`' three fields
state for each of the three keccak256 uses the quotes name.
-/

/-- `channelId` as a function of the `FixedPart` fields (S4
    `0010-states-channels.md`, "Channel IDs", quoted above). An
    uninterpreted function, not a security claim — see the module comment. -/
axiom channelIdOf : List Nat → Nat → Nat → Nat → Nat

/-- `stateHash` as a function of `(channelId, appData, outcome, turnNum,
    isFinal)` (S4 `0010-states-channels.md`, "State commitments", quoted
    above). An uninterpreted function, not a security claim. -/
axiom stateHashOf : Nat → Nat → Outcome → Nat → Bool → Nat

/-- `outcomeHash` as a function of the outcome alone (S4
    `0040-lifecycle-of-a-channel.md`, "fingerprint", quoted above: the
    `outcomeHash` argument to the fingerprint hash is a hash of the outcome
    on its own, separate from `stateHash`). Needed because `transfer` and
    `reclaim` update only the stored outcome hash, leaving `stateHash`
    unchanged (`Operations.lean`'s `transfer`/`reclaim`, following
    `MultiAssetHolder.sol:203-205,409-413`). An uninterpreted function, not
    a security claim. -/
axiom outcomeHashOf : Outcome → Nat

/-- CRYPTOGRAPHIC ASSUMPTION 1 (collision resistance of keccak256) —
    assumed, not proven. Bundles the three injectivity facts a caller
    cannot defeat: a caller cannot name two distinct `FixedPart`s with the
    same `channelId` (Nitro-2019-219.pdf §3.1, "we assume... it [is]
    impossible... to construct a channel whose address is A, if [it is]
    not previously known"); cannot present a state whose hash collides
    with a different, better-supported state; cannot swap in a different
    outcome that hashes to the one already stored for a channel. A
    theorem that reasons from a stored hash back to the unique `FixedPart`/
    state/outcome that produced it takes this structure as an explicit
    argument. -/
structure HashAssumptions where
  channelIdOf_inj :
    ∀ {p₁ p₂ : List Nat} {n₁ n₂ a₁ a₂ d₁ d₂ : Nat},
      channelIdOf p₁ n₁ a₁ d₁ = channelIdOf p₂ n₂ a₂ d₂ →
      p₁ = p₂ ∧ n₁ = n₂ ∧ a₁ = a₂ ∧ d₁ = d₂
  stateHashOf_inj :
    ∀ {c₁ c₂ : Nat} {a₁ a₂ : Nat} {o₁ o₂ : Outcome} {t₁ t₂ : Nat} {f₁ f₂ : Bool},
      stateHashOf c₁ a₁ o₁ t₁ f₁ = stateHashOf c₂ a₂ o₂ t₂ f₂ →
      c₁ = c₂ ∧ a₁ = a₂ ∧ o₁ = o₂ ∧ t₁ = t₂ ∧ f₁ = f₂
  outcomeHashOf_inj :
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
caller cannot forge any more than an ECDSA signature. Unlike `channelIdOf`,
`AuthorizedBy` is not a bare naming device: whether a digest counts as
authorized is itself the non-trivial content "a signature cannot be
forged" asserts, so the relation is a `SignatureAssumptions` field, not a
global `axiom` — any `def` or theorem that needs to ask "did `p` authorize
`d`?" must take a `SignatureAssumptions` argument to do so. -/

/-- CRYPTOGRAPHIC ASSUMPTION 2 (ECDSA / EIP-1271 unforgeability) — assumed,
    not proven. `sig.AuthorizedBy p d` holds iff participant `p` (an EOA or
    a contract) itself produced an authorization over digest `d` — an
    ECDSA signature `p`'s key signed, or an EIP-1271 acceptance `p`'s own
    code returned (`NitroUtils.isAuthorizedBy`, `NitroUtils.sol:101-126`;
    SATP §1.4, "Forging cryptographic signatures is infeasible"). Only the
    *validity* direction is needed: a call that recovers or accepts an
    authorization for `p` is constrained to a case where
    `sig.AuthorizedBy p d` already held. -/
structure SignatureAssumptions where
  AuthorizedBy : Nat → Nat → Prop

end ArmadaLean.Adjudicator
