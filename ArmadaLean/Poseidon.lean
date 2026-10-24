/-
  ArmadaLean.Poseidon — Poseidon modeled symbolically (Dolev-Yao style).

  Poseidon is the hash used everywhere in the circuits (circomlib poseidon.circom,
  instantiated at Transact.circom:63,76,81,98,108,167 and merkle.circom:40). The
  previous model took Poseidon's collision resistance as an axiom on `Nat → Nat → Nat`
  (and the 3-argument variant): `poseidon2_inj : poseidon2 a b = poseidon2 c d → a = c
  ∧ b = d`. That axiom is false of any concrete, computable function `Nat → Nat → Nat`
  — such a function's domain is strictly larger than its codomain is injective on, so a
  collision always exists; the axiom only ever asserted that no *efficient* algorithm
  finds one. A theorem whose proof rests on an axiom that is false of the function it
  names is not evidence about that function.

  This module replaces that axiom with the standard Dolev-Yao abstraction: a `Term` is
  either a raw value an attacker (or an honest prover) chose (`val`), or the symbolic
  hash of a list of terms it already holds (`hash`). Two different argument lists never
  denote the same `hash` term, and a `hash` term is never a `val` term — this holds *by
  construction*, from the inductive type's constructors (`Term.noConfusion`,
  `Term.hash.injEq`), not as an assumption about a numeric function. The soundness this
  buys: whatever an attacker can submit as a witness is built syntactically from terms
  it already has — it cannot conjure a `hash` term without supplying every one of its
  arguments, and it cannot make two syntactically different hash calls collide. This is
  the standard free-algebra abstraction of a cryptographic hash, used throughout formal
  protocol analysis (Dolev-Yao 1983); it is sound for what this project needs
  (collision resistance and domain separation) and does not model Poseidon's concrete
  field arithmetic or round structure.

  `Term.hash` takes a `List Term`, so one constructor covers every Poseidon arity the
  circuits use: 2 (note public keys, nullifiers, Merkle tree levels — `Term.hash2`
  below), 3 (commitments — `Term.hash3`), and the variable arity `2+N+M` of the EdDSA
  message hash (`msgHashOf`, ArmadaLean.Transact).
-/

/-- A term an attacker (or an honest prover) can build: either a raw number it chose
    (`val`), or the symbolic Poseidon hash of a list of terms it already holds
    (`hash`). See the module comment for why this gives collision resistance and
    domain separation by construction. -/
inductive Term where
  | val : Nat → Term
  | hash : List Term → Term

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
  | .val _, .hash _ => isFalse (fun he => Term.noConfusion he)
  | .hash _, .val _ => isFalse (fun he => Term.noConfusion he)
  | .hash l1, .hash l2 =>
    match Term.decEqList l1 l2 with
    | isTrue h => isTrue (h ▸ rfl)
    | isFalse h => isFalse (fun he => h (Term.hash.inj he))

def Term.decEqList : (l1 l2 : List Term) → Decidable (l1 = l2)
  | [], [] => isTrue rfl
  | [], _ :: _ => isFalse (fun he => absurd he (by simp))
  | _ :: _, [] => isFalse (fun he => absurd he (by simp))
  | a :: as, b :: bs =>
    match Term.decEq a b with
    | isFalse h => isFalse (fun he => h (List.cons.inj he).1)
    | isTrue h1 =>
      match Term.decEqList as bs with
      | isFalse h => isFalse (fun he => h (List.cons.inj he).2)
      | isTrue h2 => isTrue (h1 ▸ h2 ▸ rfl)
end

instance : DecidableEq Term := Term.decEq

/-- The 2-argument Poseidon hash (used for note public keys, nullifiers, and every
    Merkle tree level: merkle.circom:40). -/
def Term.hash2 (a b : Term) : Term := Term.hash [a, b]

/-- The 3-argument Poseidon hash (used for the master public key and note
    commitments: Transact.circom:63,81,108). -/
def Term.hash3 (a b c : Term) : Term := Term.hash [a, b, c]

/-- Collision resistance of `Term.hash2`, by construction: a collision forces
    argument-wise equality. The symbolic replacement for the old
    `poseidon2_inj` axiom — now a proved theorem, not an assumption. -/
theorem Term.hash2_inj {a b c d : Term} (h : Term.hash2 a b = Term.hash2 c d) :
    a = c ∧ b = d := by
  unfold Term.hash2 at h
  injection h with h'
  injection h' with ha h''
  injection h'' with hb _
  exact ⟨ha, hb⟩

/-- Collision resistance of `Term.hash3`, by construction. The symbolic replacement
    for the old `poseidon3_inj` axiom — now a proved theorem. -/
theorem Term.hash3_inj {a b c d e f : Term} (h : Term.hash3 a b c = Term.hash3 d e f) :
    a = d ∧ b = e ∧ c = f := by
  unfold Term.hash3 at h
  injection h with h'
  injection h' with ha h''
  injection h'' with hb h'''
  injection h''' with hc _
  exact ⟨ha, hb, hc⟩

/-- A `val` term is never a `hash` term, whatever their contents — domain
    separation between "a raw value an attacker chose" and "a genuine hash output",
    by construction (`Term.noConfusion`). This is the fact
    `ArmadaLean.TransactOwned.user_npk_ne_contract_npk` rests on: a user's note key is
    always built from a `hash` (the master public key), a contract's note key is
    always built from a `val` (the raw `ownerField` address), and the two can never
    collide. -/
theorem Term.val_ne_hash (n : Nat) (l : List Term) : Term.val n ≠ Term.hash l :=
  fun h => Term.noConfusion h
