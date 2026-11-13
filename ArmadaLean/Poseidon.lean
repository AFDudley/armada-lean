import Mathlib.Tactic.Says

namespace ArmadaLean

/-
  ArmadaLean.Poseidon — Poseidon and Keccak modeled symbolically (Dolev-Yao style).

  Poseidon is the hash used throughout the circuits (circomlib poseidon.circom,
  instantiated at Transact.circom:63,76,81,98,108,167 and merkle.circom:40). The
  previous model took Poseidon's collision resistance as an axiom on `Nat → Nat → Nat`
  (and the 3-argument variant): `poseidon2_inj : poseidon2 a b = poseidon2 c d → a = c
  ∧ b = d`. That axiom is false of any concrete, computable function `Nat → Nat → Nat`
  — such a function's domain is strictly larger than its codomain is injective on, so a
  collision always exists; the axiom only ever asserted that no *efficient* algorithm
  finds one. A theorem whose proof rests on an axiom that is false of the function it
  names is not evidence about that function.

  This module replaces that axiom with the standard Dolev-Yao abstraction. A `Term` is
  either a raw value an attacker (or an honest prover) chose (`val`), or the symbolic
  hash of a list of terms it already holds, TAGGED with which hash function produced it
  (`hash`). Two different argument lists never denote the same `hash` term under the
  same tag. Two different tags never denote the same `hash` term, whatever their
  argument lists. A `hash` term is never a `val` term. These three facts hold *by
  construction*, from the inductive type's constructors (`Term.noConfusion`,
  `Term.hash.injEq`).

  The free algebra is itself the cryptographic assumption. It is not a way to state no
  assumption. The old axiom declared Poseidon's collision resistance on a numeric
  function, `Nat → Nat → Nat → Nat`. This module declares the same kind of property on
  the model instead: the type gives collision freedom, domain separation, and preimage
  resistance with no further hypothesis, because it gives an attacker no operation to
  build a `hash` term except by supplying every one of its arguments, and no operation
  to read a `hash` term's arguments back out except by already holding them.
  `#print axioms` on a theorem that uses this fact lists no Poseidon or Keccak axiom.
  That does not mean the project assumes nothing about these hash functions. It means
  the assumption moved from a per-theorem hypothesis to one choice of model, made once,
  here.

  The soundness this buys: whatever an attacker can submit as a witness is built
  syntactically from terms it already has. It cannot conjure a `hash` term without
  supplying every one of its arguments. It cannot make two syntactically different hash
  calls collide. It cannot recover a hash term's arguments without already holding them.
  It cannot pass off one hash function's output as another's. This is the standard
  free-algebra abstraction of a cryptographic hash, used throughout formal protocol
  analysis (Dolev-Yao 1983). It is sound for what this project needs — collision
  resistance, domain separation, and preimage resistance, now including cross-function
  separation — and it does not model either hash's concrete field arithmetic, round
  structure, or bit width.

  The refinement from this specification to concrete code names these same three
  properties — Poseidon and Keccak collision freedom, their domain separation, and
  preimage resistance — as explicit hypotheses on the real hash functions, not as
  axioms (`docs/verification-chain.md`).

  `Term.hash` takes a `List Term`, so one constructor covers every arity either hash
  function is used at: Poseidon arity 2 (note public keys, nullifiers, Merkle tree
  levels — `Term.hash2` below), 3 (commitments — `Term.hash3`), and the variable arity
  `2+N+M` of the EdDSA message hash (`msgHashOf`, ArmadaLean.Transact); Keccak for the
  bound-parameters hash (`hashBoundParams`, ArmadaLean.BoundParams) and for address
  terms that no theorem constrains (ArmadaLean.PoolOwned's module comment on address
  terms).

  Addresses: the owned circuit's `ownerField` is a 160-bit address,
  `Term.val a` with `a < 2^160` (`ArmadaLean.Types.Address`,
  `ArmadaLean.TransactOwned`). It is never a hash term (`Term.val_ne_hash`), so a
  Dolev-Yao attacker building a witness from terms it holds can never pass an address
  off as a note key, a commitment or a nullifier, whatever number it chooses. `Term.keccak`
  stays in use for the bound-parameters hash (`ArmadaLean.BoundParams`) and for address
  terms that no theorem constrains (fee admin, treasury, tokens).
-/

/-- Which hash function produced a `Term.hash` term. The circuits use only Poseidon
    (module comment); Keccak appears once in this project, for Ethereum contract
    addresses (`ArmadaLean.PoolOwned`'s module comment on address terms). Tagging
    `Term.hash` with this is what keeps the two from ever colliding — the same
    construction that already keeps a 2-argument Poseidon call from colliding with a
    3-argument one (`Term.hash2_inj`/`Term.hash3_inj` both only ever compare terms
    carrying the same tag). -/
inductive HashFn where
  | poseidon
  | keccak
  deriving DecidableEq

/-- A term an attacker (or an honest prover) can build: either a raw number it chose
    (`val`), or the symbolic hash of a list of terms it already holds, under a named
    hash function (`hash`). See the module comment for why this gives collision
    resistance and domain separation — now including cross-function separation — by
    construction. -/
inductive Term where
  | val : Nat → Term
  | hash : HashFn → List Term → Term

/- `Term`'s equality is decidable, by mutual structural recursion with
   `Term.decEqList` over the nested `List Term` argument. The automatic `deriving
   DecidableEq` handler does not support this nested-inductive shape, so the instance
   is written out by hand; every other place in this project that needs
   `DecidableEq`/`BEq`/`LawfulBEq` on a structure containing a `Term` field
   (`ArmadaLean.PoolOwned.CommitmentPreimage`) derives it automatically from this one
   instance. -/
mutual
def Term.decEq : (a b : Term) → Decidable (a = b)
  | .val a, .val b =>
    match Nat.decEq a b with
    | isTrue h => isTrue (h ▸ rfl)
    | isFalse h => isFalse (fun he => h (Term.val.inj he))
  | .val _, .hash _ _ => isFalse (fun he => Term.noConfusion he)
  | .hash _ _, .val _ => isFalse (fun he => Term.noConfusion he)
  | .hash fn1 l1, .hash fn2 l2 =>
    match (inferInstance : DecidableEq HashFn) fn1 fn2 with
    | isFalse hfn => isFalse (fun he => hfn (Term.hash.inj he).1)
    | isTrue hfn =>
      match Term.decEqList l1 l2 with
      | isTrue hl => isTrue (hfn ▸ hl ▸ rfl)
      | isFalse hl => isFalse (fun he => hl (Term.hash.inj he).2)

def Term.decEqList : (l1 l2 : List Term) → Decidable (l1 = l2)
  | [], [] => isTrue rfl
  | [], _ :: _ => isFalse (fun he => absurd he (by (simp? says simp only [List.nil_eq, reduceCtorEq, not_false_eq_true])))
  | _ :: _, [] => isFalse (fun he => absurd he (by (simp? says simp only [reduceCtorEq, not_false_eq_true])))
  | a :: as, b :: bs =>
    match Term.decEq a b with
    | isFalse h => isFalse (fun he => h (List.cons.inj he).1)
    | isTrue h1 =>
      match Term.decEqList as bs with
      | isFalse h => isFalse (fun he => h (List.cons.inj he).2)
      | isTrue h2 => isTrue (h1 ▸ h2 ▸ rfl)
end

instance : DecidableEq Term := Term.decEq

/-- `Term` is inhabited. No theorem reads the default value. -/
instance : Inhabited Term := ⟨Term.hash .poseidon []⟩

/-- The 2-argument Poseidon hash (used for note public keys, nullifiers, and every
    Merkle tree level: merkle.circom:40). -/
def Term.hash2 (a b : Term) : Term := Term.hash .poseidon [a, b]

/-- The 3-argument Poseidon hash (used for the master public key and note
    commitments: Transact.circom:63,81,108). -/
def Term.hash3 (a b c : Term) : Term := Term.hash .poseidon [a, b, c]

/-- The Keccak-256 hash of a list of terms — EVM's `keccak256` opcode, distinct from
    Poseidon by construction (`HashFn`'s own constructors, via `Term.hash`'s tag). Used
    for the bound-parameters hash (`ArmadaLean.BoundParams.hashBoundParams`) and for
    address terms that no theorem constrains (`ArmadaLean.PoolOwned`'s module comment on
    address terms). -/
def Term.keccak (l : List Term) : Term := Term.hash .keccak l

/-- Collision resistance of `Term.hash2`, by construction: a collision forces
    argument-wise equality. The symbolic replacement for the old
    `poseidon2_inj` axiom — now a proved theorem, not an assumption. -/
theorem Term.hash2_inj {a b c d : Term} (h : Term.hash2 a b = Term.hash2 c d) :
    a = c ∧ b = d := by
  unfold Term.hash2 at h
  injection h with _ hl
  injection hl with ha h''
  injection h'' with hb _
  exact ⟨ha, hb⟩

/-- Collision resistance of `Term.hash3`, by construction. The symbolic replacement
    for the old `poseidon3_inj` axiom — now a proved theorem. -/
theorem Term.hash3_inj {a b c d e f : Term} (h : Term.hash3 a b c = Term.hash3 d e f) :
    a = d ∧ b = e ∧ c = f := by
  unfold Term.hash3 at h
  injection h with _ hl
  injection hl with ha h''
  injection h'' with hb h'''
  injection h''' with hc _
  exact ⟨ha, hb, hc⟩

/-- A `val` term is never a `hash` term, under any function tag or argument list,
    whatever their contents — domain separation between "a raw value an attacker
    chose" and "a genuine hash output", by construction (`Term.noConfusion`). -/
theorem Term.val_ne_hash (n : Nat) (fn : HashFn) (l : List Term) : Term.val n ≠ Term.hash fn l :=
  fun h => Term.noConfusion h

/-- **A Poseidon output is never a Keccak output, whatever either hash's arguments
    are.** Domain separation across hash functions, by construction
    (`HashFn.noConfusion`, via `Term.hash`'s own tag argument). Before the
    2026-11-08 design decision, `ArmadaLean.TransactOwned.user_npk_ne_contract_npk`
    rested on this fact; it now rests on `Term.val_ne_hash`, because `ownerField` is a
    160-bit address (`ArmadaLean.Types.Address`). -/
theorem Term.poseidon_ne_keccak {l1 l2 : List Term} :
    Term.hash .poseidon l1 ≠ Term.hash .keccak l2 :=
  fun h => HashFn.noConfusion (Term.hash.inj h).1

end ArmadaLean
