/-
  ArmadaLean.Adjudicator.Assumptions — two of the three facts no caller can
  change: a hash cannot be inverted or collided, and a signature cannot be
  forged.

  This model takes as given only what no caller can change: that a
  hash cannot be inverted or collided, that a signature cannot be
  forged, and that an accepted proof means its constraints hold.
  This file states the second two. The third
  (proof soundness, owned-spend circuit) now sits in `ArmadaLean.
  TransactOwned`/`ArmadaLean.PoolOwned` (root `ArmadaLean` modules,
  branch `owned-notes`): the adjudicator is an ordinary user of the
  pool, so the owned-note circuit's own assumptions belong to the pool
  module, not this adjudicator model.

  `channelIdOf`, `stateHashOf` and `outcomeHashOf` (the Nitro layer's
  keccak256 hashes) now reuse the pool layer's own symbolic Poseidon
  hash model (`ArmadaLean.Poseidon.Term`, the Dolev-Yao abstraction
  `pool-model`'s `af91ab2` introduced to replace the old
  `poseidon2_inj`/`poseidon3_inj` axioms): a `Term` is either a raw
  value (`Term.val`) or the symbolic hash of a list of terms it already
  holds (`Term.hash`). Nitro's hash is keccak256, not Poseidon, but the
  same free-algebra abstraction is sound for it too — the model needs
  only collision resistance and domain separation, not the concrete
  round structure of either hash function, and `Term` gives both BY
  CONSTRUCTION (`Term.hash.injEq`, `Term.noConfusion`), not as an
  assumption. `HashAssumptions` is consequently now an EMPTY structure:
  the three injectivity facts it used to assert as fields
  (`channelIdOf_inj`/`stateHashOf_inj`/`outcomeHashOf_inj`) are proved
  theorems below (`channelIdOf_inj`/`stateHashOf_inj`/
  `outcomeHashOf_inj`), not hypotheses — every theorem that still takes
  a `HashAssumptions` argument keeps that argument (so its approved
  statement's shape does not change), but the argument is now vacuous.
-/
import ArmadaLean.Adjudicator.Outcome

namespace ArmadaLean.Adjudicator

/-!
## Assumption 1 (was): a hash cannot be inverted or collided (Nitro layer)

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
collision resistance — is now a proved consequence of `Term`'s
constructors (module comment), not an assumed structure field.
-/

/-- `channelId` as a function of the `FixedPart` fields (S4
    `0010-states-channels.md`, "Channel IDs", quoted above): the symbolic
    hash of the four fields, participants embedded one `Term.val` each. -/
def channelIdOf (participants : List Nat) (nonce appDef challengeDuration : Nat) : Term :=
  Term.hash (participants.map Term.val ++
    [Term.val nonce, Term.val appDef, Term.val challengeDuration])

/-- `channelIdOf` is injective — PROVED, from `Term.hash`'s own
    constructor injectivity and `List.map_injective_of_injective`
    (`Outcome.lean`) lifted over the `participants` list, not assumed
    (contrast the old `HashAssumptions.channelIdOf_inj` field). -/
theorem channelIdOf_inj {p₁ p₂ : List Nat} {n₁ n₂ a₁ a₂ d₁ d₂ : Nat}
    (h : channelIdOf p₁ n₁ a₁ d₁ = channelIdOf p₂ n₂ a₂ d₂) :
    p₁ = p₂ ∧ n₁ = n₂ ∧ a₁ = a₂ ∧ d₁ = d₂ := by
  unfold channelIdOf at h
  injection h with hl
  have hlentotal : (p₁.map Term.val).length + 3 = (p₂.map Term.val).length + 3 := by
    have := congrArg List.length hl
    simpa using this
  have hlen : (p₁.map Term.val).length = (p₂.map Term.val).length := by omega
  obtain ⟨hp, htail⟩ := List.append_inj hl hlen
  have hp' : p₁ = p₂ := List.map_injective_of_injective (fun a b => Term.val.inj) p₁ p₂ hp
  simp only [List.cons.injEq] at htail
  obtain ⟨hn, ha, hd, -⟩ := htail
  exact ⟨hp', Term.val.inj hn, Term.val.inj ha, Term.val.inj hd⟩

/-- `stateHash` as a function of `(channelId, appData, outcome, turnNum,
    isFinal)` (S4 `0010-states-channels.md`, "State commitments", quoted
    above): the symbolic hash of the five fields, the outcome folded in
    via its own `Term` encoding (`Outcome.toTerm`). -/
def stateHashOf (cid : Term) (appData : Nat) (outcome : Outcome) (turnNum : Nat)
    (isFinal : Bool) : Term :=
  Term.hash [cid, Term.val appData, outcome.toTerm, Term.val turnNum,
    Term.val (if isFinal then 1 else 0)]

/-- `stateHashOf` is injective — PROVED (contrast the old
    `HashAssumptions.stateHashOf_inj` field). -/
theorem stateHashOf_inj {c₁ c₂ : Term} {a₁ a₂ : Nat} {o₁ o₂ : Outcome} {t₁ t₂ : Nat}
    {f₁ f₂ : Bool} (h : stateHashOf c₁ a₁ o₁ t₁ f₁ = stateHashOf c₂ a₂ o₂ t₂ f₂) :
    c₁ = c₂ ∧ a₁ = a₂ ∧ o₁ = o₂ ∧ t₁ = t₂ ∧ f₁ = f₂ := by
  unfold stateHashOf at h
  injection h with hl
  simp only [List.cons.injEq] at hl
  obtain ⟨h1, h2, h3, h4, h5, -⟩ := hl
  refine ⟨h1, Term.val.inj h2, Outcome.toTerm_inj h3, Term.val.inj h4, ?_⟩
  have hf := Term.val.inj h5
  cases f₁ <;> cases f₂ <;> simp_all

/-- `outcomeHash` as a function of the outcome alone (S4
    `0040-lifecycle-of-a-channel.md`, "fingerprint", quoted above: the
    `outcomeHash` argument to the fingerprint hash is a hash of the outcome
    on its own, separate from `stateHash`). Needed because `transfer` and
    `reclaim` update only the stored outcome hash, leaving `stateHash`
    unchanged (`Operations.lean`'s `transfer`/`reclaim`, following
    `MultiAssetHolder.sol:203-205,409-413`). Literally `Outcome.toTerm`
    (`Outcome.lean`) under this name, for parity with `channelIdOf`/
    `stateHashOf`'s own naming at every call site. -/
def outcomeHashOf (o : Outcome) : Term := o.toTerm

/-- `outcomeHashOf` is injective — PROVED (`Outcome.toTerm_inj`), contrast
    the old `HashAssumptions.outcomeHashOf_inj` field. -/
theorem outcomeHashOf_inj {o₁ o₂ : Outcome} (h : outcomeHashOf o₁ = outcomeHashOf o₂) :
    o₁ = o₂ := Outcome.toTerm_inj h

/-- CRYPTOGRAPHIC ASSUMPTION 1 (collision resistance of keccak256) — now an
    EMPTY structure: every fact it used to assert as a field is a proved
    theorem above (module comment). Every theorem that reasons from a
    stored hash back to the unique `FixedPart`/state/outcome that produced
    it still takes this structure as an explicit argument, so its approved
    statement's shape is unchanged; the argument itself is now vacuous. -/
structure HashAssumptions where


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
  contractAuthorizes : Nat → Term → Prop

end ArmadaLean.Adjudicator
