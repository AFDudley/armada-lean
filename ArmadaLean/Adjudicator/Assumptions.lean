/-
  ArmadaLean.Adjudicator.Assumptions — two of the three facts no caller can
  change: a hash cannot be inverted or collided, and a signature cannot be
  forged.

  This model takes as given only what no caller can change: that a
  hash cannot be inverted or collided, that a signature cannot be
  forged, and that an accepted proof means its constraints hold.
  This file states the first two. The third
  (proof soundness, owned-spend circuit) now sits in `ArmadaLean.
  TransactOwned`/`ArmadaLean.PoolOwned` (root `ArmadaLean` modules,
  branch `owned-notes`): the adjudicator is an ordinary user of the
  pool, so the owned-note circuit's own assumptions belong to the pool
  module, not this adjudicator model.

  Each assumption is a FIELD of a named structure (`HashAssumptions`,
  `SignatureAssumptions`), never a bare global `axiom`. A bare axiom is a
  fact any proof anywhere can invoke without the theorem's own signature
  showing it; a structure a theorem takes as an explicit argument forces
  the dependency onto the type, so a reader sees from the statement alone
  which assumptions it needs.
  `channelIdOf`, `stateHashOf` and `outcomeHashOf` stay as bare `axiom`
  declarations: each names an uninterpreted FUNCTION with no asserted
  property (the same status as `decodeGuarantee`), not a security claim —
  the security claim is their INJECTIVITY, which is a `HashAssumptions`
  field below. The application rule is NOT a bare axiom either, but a
  PARAMETER of the model (`Operations.lean`'s `Step`, `appRel`) — see
  that file's module comment.

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

Clause 8: "A signature counts for participant i if i signed as an EOA, or,
when i is a contract, if i accepts the signature through EIP-1271." Two
genuinely different mechanisms, not one relation:

1. The EOA path is an ACTION a participant takes: they choose to sign a
   digest, or they do not. Only the key holder can take it. Nitro-
   2019-219.pdf §3.1: "Given an address, A, we assume that the properties
   of the signature scheme and hashing algorithm make it impossible to
   find a private key for A... if they are not previously known"; the
   withdrawal operation "can be used to withdraw coins held at
   participant address, A, by any party with the knowledge of the
   corresponding private key" — authority comes from HOLDING the key.
   SATP §1.4, "Our contribution", the two security assumptions named
   before Theorem 3.2's informal preview: "(Safety) Forging cryptographic
   signatures is infeasible." ForceMove-2018.pdf §3.1.3, "Moves and
   states": "A move consists of a State and a (cryptographic) signature...
   From the signature you can deduce the signer – the participant who
   signed the move." §2.2's worked example: Bob "needs signatures from
   both parties to launch a challenge" — he needs to HOLD them, not
   produce them himself for Alice.

   None of the three sources lets a caller produce a signature for a key
   they do not hold; `NitroUtils.sol:101-126`'s `signer == participant`
   check lets anyone SUBMIT signature bytes that already exist (clause 8;
   Nitro-2019-219.pdf §3.3, "There is no restriction on who can trigger
   the operations"), which is a fact about relaying bytes, not about who
   may produce them — submitting is not signing. This model records
   signing as part of the EXECUTION, not as a structure field: a
   structure field with no constraining axiom can be satisfied by an
   always-true relation, asserting every participant signed every digest,
   which none of the three sources above supports. `State.lean`'s
   `AdjudicatorState.signedBy` and `Operations.lean`'s `.sign` `Call`
   carry it instead, gated on an explicit `Actor` matching the digest's
   own participant (`Operations.lean`'s module comment) — this is where
   unforgeability of the EOA path lives: in who may TAKE the step, not
   only in which row the step's effect touches.
2. The EIP-1271 path is a FIXED fact about a contract's already-deployed
   code: whether `participant.code` accepts a given digest does not change
   call to call, and no caller can change it either. This stays a
   structure field below, `contractAuthorizes` — the same discipline as
   `channelIdOf`: an opaque, caller-independent function, safe to leave
   unconstrained because nothing in this model claims a specific contract
   accepts anything in particular.

`State.lean`'s `AuthorizedBy sig s p d := s.signedBy p d ∨ sig.
contractAuthorizes p d` combines both paths, the same union
`NitroUtils.isAuthorizedBy` computes. -/

/-- CRYPTOGRAPHIC ASSUMPTION 2, EIP-1271 half (a contract cannot be made to
    accept an authorization its own code would refuse) — assumed, not
    proven. `sig.contractAuthorizes p d` holds iff participant `p`, if a
    contract, accepts digest `d` through its own `isValidSignature`
    (`NitroUtils.isAuthorizedBy`, `NitroUtils.sol:101-126`, the EIP-1271
    branch). A fixed fact about already-deployed code; no caller changes
    it by calling anything. The EOA half of assumption 2 — a participant
    can authorize a digest only by their own `.sign` action, and no caller
    can sign on another participant's behalf — lives in `State.lean`'s
    `AdjudicatorState.signedBy` and `Operations.lean`'s `.sign` `Call`,
    not here (see the module comment above). -/
structure SignatureAssumptions where
  contractAuthorizes : Nat → Nat → Prop

end ArmadaLean.Adjudicator
