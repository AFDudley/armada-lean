/-
  ArmadaLean.PoolSafety — the pool contract's safety theorems, over ArmadaLean.Pool.

  `transactOwned`/`verifyOwned` citations below name an open pull request, not
  yet merged into `main`: `ArmadaLean.PoolOwned`'s header gives the PR. Every
  `TransactModule.sol:N` citation with `N` past line 498 of `main`, and every
  `PrivacyPoolStorage.sol:N` citation with `N` past line 236, names that PR,
  not `main`.
-/
import ArmadaLean.Pool
import ArmadaLean.PoolMachine
import ArmadaLean.Types.Reachable
import ArmadaLean.SpecTools
import Mathlib.Tactic.Says

namespace ArmadaLean

/-! ### The core invariant: tokens held equal the value of unspent notes -/

/-- The core invariant: for each token, the tokens the pool holds equal the total value
    of its unspent notes, summed over live leaf positions. -/
def HeldInvariant (s : PoolState) : Prop :=
  ∀ t, s.held t = listSum ((s.live t).map (fun p => p.2.value))

theorem genesis_invariant (r : FeeRatio) (feeAdmin treasury : Term) :
    HeldInvariant (genesis r feeAdmin treasury) := by
  intro t
  (simp? [genesis, listSum] says simp only [genesis, List.map_nil, listSum])

/-- The value projection of a `List.ofFn`-built list of notes, all sharing one `token`
    and one key-derivation `mk`, is exactly the underlying value function. Bridges the
    circuit's `Fin`-indexed `valueIn`/`valueOut` and the pool's `List`-indexed note
    bookkeeping everywhere below. `mk` produces note public keys, hence `Term`. -/
theorem value_ofFn_eq {N : Nat} (mk : Fin N → Term) (g : Fin N → Nat) (token : Token) :
    (List.ofFn (fun i => (⟨mk i, token, g i⟩ : CommitmentPreimage))).map
        CommitmentPreimage.value = List.ofFn g := by
  rw [List.map_ofFn]
  rfl

/-- The position-tagged counterpart of `value_ofFn_eq`: tagging each note with a
    position (`transactSpentPositions`/`ownedSpentPositions`'s own shape, now
    `(treeNumber, leafIndex)` pairs) does not touch the value projection. Polymorphic
    in the tag type `β`, since the tag is now a pair, not a bare `Nat`. -/
theorem value_ofFn_pos_eq {N : Nat} {β : Type} (pos : Fin N → β) (mk : Fin N → Term)
    (g : Fin N → Nat) (token : Token) :
    (List.ofFn (fun i => (pos i, (⟨mk i, token, g i⟩ : CommitmentPreimage)))).map
        (fun p => p.2.value) = List.ofFn g := by
  rw [List.map_ofFn]
  rfl

/-- **The balance a `Step.transact` moves is derived, not assumed.** `transactSpentPositions`
    and `transactAllOutputs` are built straight from the witness; `transact_value_conserved`
    (`ArmadaLean.Transact`) — which needs exactly the registered-shape bound `hN`/`hM` to
    upgrade the circuit's mod-`p` equality to an integer one — gives their values' sum
    equality, and `UnshieldRefines` carries that equality across the split into new
    notes and the unshield amount. This is the fact `Step.transact`'s own comment points
    to instead of taking it as a hypothesis. -/
theorem transact_balance {N M : Nat} {w : TransactWitness N M} {pub : TransactPublic N M}
    (treeNumber : Nat) (hN : N ≤ 8) (hM : M ≤ 4) (hC : Constrained w pub)
    {u : Option Unshield} {newNotes : List CommitmentPreimage}
    (hOutputs : UnshieldRefines w u newNotes) :
    listSum ((transactSpentPositions treeNumber w).map (fun p => p.2.value)) =
      listSum (newNotes.map CommitmentPreimage.value) + withdrawn u := by
  have hbal := transact_value_conserved w pub hN hM hC
  have hvals : listSum ((transactAllOutputs w).map CommitmentPreimage.value) =
      listSum (newNotes.map CommitmentPreimage.value) + withdrawn u := by
    cases u with
    | none =>
      simp only [UnshieldRefines] at hOutputs
      rw [hOutputs, withdrawn, Nat.add_zero]
    | some v =>
      simp only [UnshieldRefines] at hOutputs
      rw [hOutputs, List.map_append, listSum_append, withdrawn]
      (simp? [listSum] says simp only [List.map_cons, List.map_nil, listSum, Nat.add_zero, Nat.add_left_cancel_iff])
  unfold transactAllOutputs at hvals
  rw [value_ofFn_eq] at hvals
  unfold transactSpentPositions
  rw [value_ofFn_pos_eq, hbal, hvals]

/-- The new notes of a transact are at most the circuit's `M` outputs. -/
theorem unshieldRefines_length_le {N M : Nat} {w : TransactWitness N M}
    {u : Option Unshield} {newNotes : List CommitmentPreimage}
    (h : UnshieldRefines w u newNotes) : newNotes.length ≤ M := by
  cases u with
  | none =>
    simp only [UnshieldRefines] at h
    have hl := congrArg List.length h
    simp only [transactAllOutputs, List.length_ofFn] at hl
    omega
  | some v =>
    simp only [UnshieldRefines] at h
    have hl := congrArg List.length h
    simp only [transactAllOutputs, List.length_ofFn, List.length_append,
      List.length_singleton] at hl
    omega

/-- Every new note of a transact is one of the circuit's outputs. -/
theorem unshieldRefines_mem {N M : Nat} {w : TransactWitness N M}
    {u : Option Unshield} {newNotes : List CommitmentPreimage}
    (h : UnshieldRefines w u newNotes) : ∀ x ∈ newNotes, x ∈ transactAllOutputs w := by
  intro x hx
  cases u with
  | none =>
    simp only [UnshieldRefines] at h
    rw [h]; exact hx
  | some v =>
    simp only [UnshieldRefines] at h
    rw [h]; exact List.mem_append_left _ hx

/-- The owned-path counterpart of `transact_balance`: no unshield split, since
    `transactOwned` never unshields. -/
theorem transactOwned_balance {N M : Nat} {w : TransactOwnedWitness N M}
    {pub : TransactOwnedPublic N M} (treeNumber : Nat) (hN : N ≤ 8) (hM : M ≤ 4)
    (hC : OwnedConstrained w pub) :
    listSum ((ownedSpentPositions treeNumber pub w).map (fun p => p.2.value)) =
      listSum ((ownedNewNotes w).map CommitmentPreimage.value) := by
  have hbal := transactOwned_value_conserved w pub hN hM hC
  unfold ownedSpentPositions ownedNewNotes
  rw [value_ofFn_pos_eq, value_ofFn_eq]
  exact hbal

theorem step_preserves_invariant {s s' : PoolState} (hinv : HeldInvariant s)
    (hstep : Step s s') : HeldInvariant s' := by
  cases hstep with
  | setFeeRatio => exact hinv
  | shield token x npk hValue hSpendable =>
    intro t
    by_cases ht : t = token
    · simp only [ht, if_pos]
      have hinv_t := hinv token
      simp only [List.map_cons, listSum]
      omega
    · simp only [if_neg ht]
      exact hinv t
  | transact caller w pub bp hN hM hC hBound hAdapt newNotes hOutputs rest spent' records
      openings hRoot hRemove hNullify hRecords =>
    intro t
    by_cases ht : t = w.token
    · subst ht
      simp only [if_pos]
      have hsum := removeAll_sum (fun p => p.2.value) hRemove
      have hbal := transact_balance bp.treeNumber hN hM hC hOutputs
      have hinv_t := hinv w.token
      have hpos := withTreePositionsFrom_map CommitmentPreimage.value
        (insertTree s.trees newNotes.length)
        (insertStart s.trees newNotes.length) newNotes
      simp only [List.map_append, listSum_append]
      rw [hpos]
      omega
    · simp only [if_neg ht]
      exact hinv t
  | transactOwned w pub bp hN hM hC caller hCaller hBound hAdapt hNoUnshield rest spent'
      openings hRoot hRemove hNullify =>
    intro t
    by_cases ht : t = w.token
    · subst ht
      simp only [if_pos]
      have hsum := removeAll_sum (fun p => p.2.value) hRemove
      have hbal := transactOwned_balance bp.treeNumber hN hM hC
      have hinv_t := hinv w.token
      have hpos := withTreePositionsFrom_map CommitmentPreimage.value
        (insertTree s.trees (ownedNewNotes w).length)
        (insertStart s.trees (ownedNewNotes w).length) (ownedNewNotes w)
      simp only [List.map_append, listSum_append]
      rw [hpos]
      omega
    · simp only [if_neg ht]
      exact hinv t

/--
**The core invariant, over every reachable state.** For each token, the tokens the pool
holds equal the total value of its unspent notes. Rules out the pool ever holding tokens
no live note backs (insolvency) and the pool ever owing more than it holds (a note whose
value is not actually backed). Proved by induction on `Reachable`: the genesis state
trivially satisfies it (no tokens, no notes), and `step_preserves_invariant` shows every
`Step` preserves it, using `transact_balance`/`transactOwned_balance` (which themselves
derive from `transact_value_conserved`/`transactOwned_value_conserved` under the
registered-shape bound `hN`/`hM`, not an assumed hypothesis) for
`transact`/`transactOwned`, and direct construction for `shield`.
Sources. Each step moves tokens and note value by the same amount: a shield pulls exactly
the note's value into the pool and checks the received amount,
`require(balanceAfter - balanceBefore == base, …)` (ShieldModule.sol:300-309); an unshield
pays exactly the unshield note's value out, `token.safeTransfer(recipient, _note.value)`
(TransactModule.sol:434); a spend marks each input note's nullifier once
(TransactModule.sol:392-398); and a proof's inputs equal its outputs, `sumIn === sumOut`
(Transact.circom:143 at commit `e79919d`). S-RG ("RAILGUN Core System & Protocol",
`ArmadaLean.Pool` module comment) states the same split: "Deposit amount + input amounts =
withdrawal amount + output amounts, so no one can create tokens out of thin air", and the
contract "transfers tokens from the user wallet to itself … or transfers tokens from itself
to the specified user wallet address". armada-poc states this exact invariant as a Foundry
invariant test, `invariant_poolCoversUnspentNotesPerToken`: `assertEq(usdc.balanceOf(address(pool)),
handler.ghostTotal(address(usdc)), "USDC notes not backed")`
(PrivacyPoolSolvencyInvariant.t.sol:617-621). RAILGUN's documentation: "The Merkle Tree keeps track of all
balances held by 0zk addresses in the system which can only be updated if proof that passes
the cryptographic validation rules is submitted to the RAILGUN smart contracts"
(docs.railgun.org/wiki/learn/using-private-tokens, line 5). -/
theorem core_invariant (s : ReachableState Pool.machine) :
    HeldInvariant s.state := by
  obtain_reach ⟨s, h : Reachable s⟩ := s
  induction h with
  | genesis r a b => exact genesis_invariant r a b
  | step _ hstep ih => exact step_preserves_invariant ih hstep

/-! ### Ownership: a spend can only touch notes its spender derives keys for -/

/--
**A transact spends only notes whose owner key derives from keys the spender holds.** If
a `Step.transact`'s input `i` opens the same commitment as a note genuinely created for
master public key `trueMpk` (`hSameNote`), `ArmadaLean.Transact.commitment_mpk_inj` forces
the witness's own derived key, `masterPublicKey w.publicKey w.nullifyingKey`, to equal
`trueMpk` — and `Constrained.sig` (the circuit's EdDSA check, Transact.circom:142-150)
already requires a signature by `w.publicKey` that verifies, which, under "a signature
cannot be forged" (the brief's named assumption), only the true holder of `w.publicKey`'s
private key can produce. This is the first harm the brief names, for the plain path: no
caller can take tokens no unspent note of theirs backs, because no caller without
`trueMpk`'s private key can build a `Constrained` witness opening `trueMpk`'s note. The
plain-path counterpart of `ArmadaLean.PoolOwned.owned_owner_binding`. -/
theorem transact_spends_only_owned {N M : Nat} {w : TransactWitness N M}
    {pub : TransactPublic N M} (hC : Constrained w pub) (i : Fin N)
    {trueMpk : Term} {trueRandom : Nat}
    (hSameNote :
      commitment (npk (masterPublicKey w.publicKey w.nullifyingKey) (w.randomIn i)) w.token
        (w.valueIn i) =
      commitment (npk trueMpk trueRandom) w.token (w.valueIn i)) :
    masterPublicKey w.publicKey w.nullifyingKey = trueMpk ∧
      EdDSAVerify w.publicKey w.signature (msgHashOf pub) :=
  ⟨commitment_mpk_inj hSameNote, hC.sig⟩

/--
**An owned transact spends only notes owned by the calling contract.** Direct
restatement of `ArmadaLean.PoolOwned.owned_owner_binding` at the point `Step.transactOwned`
is built: the `hC`/`caller`/`hCaller` a `Step.transactOwned` term already requires are
exactly what this needs. If input `i`'s true creator was `trueOwner` (`hSameNote`: the
spent commitment is the one `trueOwner` genuinely created), the step's `caller` must be
`trueOwner`'s own address — the second half of the brief's first harm, for the owned
path.
Source: TransactModule.sol:636-639. -/
theorem transactOwned_spends_only_owned {N M : Nat} {w : TransactOwnedWitness N M}
    {pub : TransactOwnedPublic N M} (hC : OwnedConstrained w pub) (i : Fin N)
    {trueOwner : Term} {trueRandom : Nat}
    (hSameNote :
      commitment (npk pub.ownerField (w.randomIn i)) w.token (w.valueIn i) =
      commitment (npk trueOwner trueRandom) w.token (w.valueIn i))
    {caller : Term} (hCaller : caller = pub.ownerField) :
    caller = trueOwner :=
  owned_owner_binding hC i hSameNote hCaller

/-! ### No double spend across transactions -/

/-- A successful `markSpent` call never drops a nullifier that was already marked: it
    only ever grows the set (`markSpent`'s recursive case prepends, it never removes). -/
theorem markSpent_subset {spent spent' : NullifierSet} {ns : List Term}
    (h : markSpent spent ns = some spent') : ∀ n ∈ spent, n ∈ spent' := by
  induction ns generalizing spent with
  | nil =>
    unfold markSpent at h
    cases h
    exact fun n hn => hn
  | cons n ns ih =>
    unfold markSpent at h
    by_cases hmem : n ∈ spent
    · rw [if_pos hmem] at h; exact absurd h (by (simp? says simp only [reduceCtorEq, not_false_eq_true]))
    · rw [if_neg hmem] at h
      intro m hm
      exact ih h m (List.mem_cons_of_mem n hm)

/-- A successful `markSpent` call's result set is exactly `spent` plus `ns` (as a
    bound): every element of the result came from one or the other. The converse half
    of `markSpent_subset`, needed by `live_note_unspent` to trace a newly-spent
    nullifier back to the specific input that produced it. -/
theorem markSpent_superset {spent spent' : NullifierSet} {ns : List Term}
    (h : markSpent spent ns = some spent') : ∀ n ∈ spent', n ∈ spent ∨ n ∈ ns := by
  induction ns generalizing spent with
  | nil =>
    unfold markSpent at h
    cases h
    exact fun n hn => Or.inl hn
  | cons n ns ih =>
    unfold markSpent at h
    by_cases hmem : n ∈ spent
    · rw [if_pos hmem] at h; exact absurd h (by (simp? says simp only [reduceCtorEq, not_false_eq_true]))
    · rw [if_neg hmem] at h
      intro m hm
      rcases ih h m hm with hcase | hcase
      · rcases List.eq_or_mem_of_mem_cons hcase with heq | hcase2
        · exact Or.inr (heq ▸ List.mem_cons_self)
        · exact Or.inl hcase2
      · exact Or.inr (List.mem_cons_of_mem n hcase)

/-- A successful `markSpent` call marks every nullifier of its batch. -/
theorem markSpent_mem {spent spent' : NullifierSet} {ns : List Term}
    (h : markSpent spent ns = some spent') : ∀ n ∈ ns, n ∈ spent' := by
  induction ns generalizing spent with
  | nil => intro n hn; exact absurd hn List.not_mem_nil
  | cons m ms ih =>
    unfold markSpent at h
    by_cases hm : m ∈ spent
    · rw [if_pos hm] at h
      exact absurd h (by (simp? says simp only [reduceCtorEq, not_false_eq_true]))
    · rw [if_neg hm] at h
      intro n hn
      rcases List.mem_cons.mp hn with hn | hn
      · exact hn ▸ markSpent_subset h m List.mem_cons_self
      · exact ih h n hn

/-- One step never un-spends a nullifier, in any one tree. `spent` is now per-tree
    (`PrivacyPoolStorage.nullifiers`, `treeNumber -> nullifier -> isSpent`,
    PrivacyPoolStorage.sol:174): a step only ever updates tree `treeNumber`'s own
    nullifier set, so for any other tree `s'.spent tn = s.spent tn` trivially, and for
    `tn = treeNumber`, `markSpent_subset` closes it. -/
theorem spent_monotone {s s' : PoolState} (hstep : Step s s') (tn : Nat) :
    ∀ n ∈ s.spent tn, n ∈ s'.spent tn := by
  cases hstep with
  | setFeeRatio => exact fun n hn => hn
  | shield token x npk hValue hSpendable =>
    exact fun n hn => hn
  | transact caller w pub bp hN hM hC hBound hAdapt newNotes hOutputs rest spent' records
      openings hRoot hRemove hNullify hRecords =>
    generalize bp.treeNumber = treeNumber at hRoot hRemove hNullify ⊢
    by_cases htn : tn = treeNumber
    · subst tn; simp only; exact markSpent_subset hNullify
    · simp only [if_neg htn]; exact fun n hn => hn
  | transactOwned w pub bp hN hM hC caller hCaller hBound hAdapt hNoUnshield rest spent'
      openings hRoot hRemove hNullify =>
    generalize bp.treeNumber = treeNumber at hRoot hRemove hNullify ⊢
    by_cases htn : tn = treeNumber
    · subst tn; simp only; exact markSpent_subset hNullify
    · simp only [if_neg htn]; exact fun n hn => hn

/-- Reachability relative to a starting state, for stating "once spent, a nullifier
    stays spent for the rest of the pool's history" without re-deriving the whole
    history from genesis every time. -/
inductive ReachableFrom : PoolState → PoolState → Prop where
  | refl {s} : ReachableFrom s s
  | step {s s' s'' : PoolState} (h : ReachableFrom s s') (hstep : Step s' s'') :
      ReachableFrom s s''

/-- A nullifier spent at the start of a history stays spent throughout it, in the tree
    it was spent in. -/
theorem spent_monotone_from {s s' : PoolState} (h : ReachableFrom s s') (tn : Nat) :
    ∀ n ∈ s.spent tn, n ∈ s'.spent tn := by
  induction h with
  | refl => exact fun n hn => hn
  | step _ hstep ih => exact fun n hn => spent_monotone hstep tn n (ih n hn)

/--
**No double spend across transactions.** If a nullifier `n` is already spent in tree
`tn` at a reachable state `s0`, then at any later point `s` in the same history
(`ReachableFrom s0 s`), no `transact`/`transactOwned` call against tree `tn` can mark
`n` again: `n` is not among the nullifiers any successful `markSpent` call against tree
`tn`'s own spent set processes. Proved by combining `spent_monotone_from` (`n` is still
in `s.spent tn`, since spending never un-marks a nullifier) with
`ArmadaLean.PoolOwned.owned_no_double_spend` (a successful `markSpent` call's
nullifiers are all fresh against the *current* spent set — the same freshness check
covers `transact` and `transactOwned`, since both call `_accumulateAndNullify`,
TransactModule.sol:385-411). S-RG, "RAILGUN Core System & Protocol": "The contract
checks to make sure: ... That it hasn't seen the nullifiers before, eliminating any
double spends." -/
theorem pool_no_double_spend (s0 : ReachableState Pool.machine) {s : PoolState}
    (hfrom : ReachableFrom s0.state s) (tn : Nat)
    {n : Term} (hn0 : n ∈ s0.state.spent tn) {ns : List Term} {spent' : NullifierSet}
    (hmark : markSpent (s.spent tn) ns = some spent') : n ∉ ns := by
  obtain_reach ⟨s0, _h0 : Reachable s0⟩ := s0
  intro hmem
  exact (owned_no_double_spend hmark).2 n hmem (spent_monotone_from hfrom tn n hn0)

/-! ### Two different live positions never share a nullifier -/

/--
**Two different leaf positions never share a nullifier.** `nullifier`'s two
arguments combine in one `Term.hash2` call
(`ArmadaLean.Nullifier.nullifier_pos_inj`), so for any one spender's key (plain
`nullifyingKey` or owned `ownerField` alike — `nullifier` does not distinguish the
two), distinct leaf positions always derive distinct nullifiers. This is the fact that
makes identifying a live note by its position sound in the first place: `PoolState
.live`'s `((treeNumber, position), preimage)` entries (module comment, Pool.lean) can
never be confused by the nullifier a spend proof publishes for one of them, because no
other live position could ever produce that same nullifier under the same key.
Source: Transact.circom:97-101, TransactOwned.circom:89-97. -/
theorem live_positions_distinct_nullifiers {nk : Term} {p₁ p₂ : Nat} (hpos : p₁ ≠ p₂) :
    nullifier nk p₁ ≠ nullifier nk p₂ :=
  fun h => hpos (nullifier_pos_inj h)

/-! ### A spend removes exactly what it spends, and adds exactly its new notes -/

/--
**A spend removes exactly the positions it names from the live set, and adds exactly
its new notes.** Before the step, the live entries of the spent token are exactly the
named `spentPositions` plus a remainder (`removeAll_perm`, a multiset statement: two
positions are never confused with each other,
`ArmadaLean.Nullifier.nullifier_pos_inj`/`live_positions_distinct_nullifiers`, but the
removal itself is already unambiguous purely by position equality). After the step,
the live entries of that token are exactly the new notes, tagged with the leaf
positions and tree number they land at (`withTreePositionsFrom`), plus that same
remainder, by `Step.transact`/`Step.transactOwned`'s own construction (where
`spentPositions` is always `transactSpentPositions treeNumber w`/`ownedSpentPositions
treeNumber pub w`, read off the proof's own witness — never a free choice,
`ArmadaLean.PoolSafety.transact_spends_only_owned`/`.transactOwned_spends_only_owned`).
A spend of a position that is not live in that tree has no step: `removeAll` returns
`none` the moment a requested position is missing, so no `Step.transact`/`.transactOwned`
term can be built at all. S-RG, "How Does RAILGUN Work?": "The input notes are moved
from the live pool to the dead pool, and the output notes are added to the live pool."
(Armada keeps no separate dead pool — a spent note stays in the Merkle tree, only its
nullifier is marked — so "moved to the dead pool" corresponds here to "removed from
`live`", the model's own live-note bookkeeping.) -/
theorem spend_live_exact {s : PoolState} {token : Token}
    {spentPositions : List ((Nat × Nat) × CommitmentPreimage)}
    {newNotes : List CommitmentPreimage} {rest : List ((Nat × Nat) × CommitmentPreimage)}
    (treeNumber startPos : Nat)
    (hRemove : removeAll (s.live token) spentPositions = some rest) :
    (s.live token).Perm (spentPositions ++ rest) ∧
      ({ s with
          live := fun t => if t = token
              then withTreePositionsFrom treeNumber startPos newNotes ++ rest else s.live t } :
        PoolState).live token = withTreePositionsFrom treeNumber startPos newNotes ++ rest :=
  ⟨removeAll_perm hRemove, by (simp? says simp only [↓reduceIte])⟩

/--
**An unshield pays exactly one recipient exactly the spent value minus the value of the
new notes.** For a `Step.transact` whose bound parameters carry the unshield `u`, the
step's payout record gains exactly `⟨w.token, u.recipient, u.value⟩`, the pool's
custody of the token falls by exactly `u.value`, and `u.value` is the spent notes'
value minus the new notes' value (`transact_balance`, derived from
`transact_value_conserved`, not assumed). The recipient and the amount come from the
bound parameters, which the proof binds (`hBound`); the contract carries them in the
last output commitment (`UnshieldRefines`, finding P-7). S-RG, "RAILGUN Core System &
Protocol": the contract "transfers tokens from itself to the specified user wallet
address in the public inputs, if a withdrawal amount is specified". -/
theorem transact_unshield_exact {s : PoolState} (caller : Term) {N M : Nat}
    (w : TransactWitness N M) (pub : TransactPublic N M) (bp : BoundParams)
    (hN : N ≤ 8) (hM : M ≤ 4) (hC : Constrained w pub)
    (hBound : pub.boundParamsHash = hashBoundParams bp) (hAdapt : AdaptAllows bp caller)
    (newNotes : List CommitmentPreimage) (hOutputs : UnshieldRefines w bp.unshield newNotes)
    (rest : List ((Nat × Nat) × CommitmentPreimage)) (spent' : NullifierSet)
    (records : List (Term × CommitmentPreimage)) (openings : List (Term × OwnedOpening))
    (hRoot : pub.merkleRoot ∈ s.rootsAt' bp.treeNumber)
    (hRemove : removeAll (s.live w.token) (transactSpentPositions bp.treeNumber w) = some rest)
    (hNullify : markSpent (s.spent bp.treeNumber) (List.ofFn pub.nullifiers) = some spent')
    (hRecords : records.Sublist (transactOutputRecords w pub))
    {u : Unshield} (hU : bp.unshield = some u) :
    ∃ s', Step s s' ∧
      s'.payouts = s.payouts ++ [⟨w.token, u.recipient, u.value⟩] ∧
      s'.held w.token = s.held w.token - u.value ∧
      u.value = listSum ((transactSpentPositions bp.treeNumber w).map (fun p => p.2.value)) -
        listSum (newNotes.map CommitmentPreimage.value) := by
  have hbal := transact_balance bp.treeNumber hN hM hC hOutputs
  rw [hU] at hbal
  simp only [withdrawn] at hbal
  refine ⟨_, Step.transact caller w pub bp hN hM hC hBound hAdapt newNotes hOutputs rest spent'
    records openings hRoot hRemove hNullify hRecords, by (simp? [hU] says simp only [hU, Option.map_some, Option.toList_some]), by (simp? [hU, withdrawn] says simp only [↓reduceIte, withdrawn, hU]), ?_⟩
  omega

/--
**A shield of the gross amount `x` creates exactly one note of `shieldBase r x`, at a
fresh position, and pays `shieldFee r x` to the treasury.** `r` is the deployment fee
rate `s.feeRatio`. By `Step.shield`'s construction: some tree `tn` and position `pos`
had no leaf before the step (`(s.leavesAt' tn)[pos]? = none`) and hold the new note's
commitment after it; the live set of the shielded token gains exactly the entry
`((tn, pos), ⟨npk, token, shieldBase r x⟩)`; the pool's custody of that token rises by
exactly `shieldBase r x`; the treasury's fees of that token rise by exactly
`shieldFee r x`; the two parts add up to `x` (`fee_conservation`); nothing changes for
any other token; no second ("fee") note is created. Contract: `_validateCommitmentPreimage`
(ShieldModule.sol:244), `_transferTokenIn` (ShieldModule.sol:324-340), `_getFee`
(ShieldModule.sol:353-371), insertion (ShieldModule.sol:79-83). No capacity hypothesis:
a full tree rolls over (`insertLeaves`). S-RG, "RAILGUN Core System & Protocol": "Then
the smart contract transfers tokens from the user wallet to itself, if a deposit amount
is specified ... The hashes of the output UTXOs are then added to the Merkle tree." -/
theorem shield_creates_exactly {s : PoolState} (token : Token) (x : Nat) (npk : Term)
    (hValue : 0 < x) (hSpendable : Spendable (shieldBase s.feeRatio x)) :
    ∃ s', Step s s' ∧ ∃ tn pos : Nat,
      (s.leavesAt' tn)[pos]? = none ∧
      (s'.leavesAt' tn)[pos]? = some (hashCommitment ⟨npk, token, shieldBase s.feeRatio x⟩) ∧
      s'.live token =
        ((tn, pos), (⟨npk, token, shieldBase s.feeRatio x⟩ : CommitmentPreimage)) :: s.live token ∧
      s'.held token = s.held token + shieldBase s.feeRatio x ∧
      s'.treasuryFees token = s.treasuryFees token + shieldFee s.feeRatio x ∧
      shieldBase s.feeRatio x + shieldFee s.feeRatio x = x ∧
      (∀ t, t ≠ token → s'.live t = s.live t ∧ s'.held t = s.held t ∧
        s'.treasuryFees t = s.treasuryFees t) := by
  refine ⟨_, Step.shield token x npk hValue hSpendable, insertTree s.trees 1,
    insertStart s.trees 1, ?_, ?_, by (simp? says simp only [↓reduceIte]), by (simp? says simp only [↓reduceIte, Nat.add_left_cancel_iff]), by (simp? says simp only [↓reduceIte, Nat.add_left_cancel_iff]), fee_conservation s.feeRatio x,
    fun t ht => ⟨by (simp? [ht] says simp only [ht, ↓reduceIte]), by (simp? [ht] says simp only [ht, ↓reduceIte]), by (simp? [ht] says simp only [ht, ↓reduceIte])⟩⟩
  · (simp? [PoolState.leavesAt', insertStart_eq] says simp only [PoolState.leavesAt', insertStart_eq, Nat.lt_irrefl, not_false_eq_true, getElem?_neg])
  · show (leavesAt (insertLeaves s.trees [_]) (insertTree s.trees 1))[insertStart s.trees 1]? = _
    rw [insertLeaves_leavesAt, if_pos (by rfl), insertStart_eq]
    (simp? says simp only [List.length_append, List.length_cons, List.length_nil, Nat.zero_add, Nat.lt_add_one, getElem?_pos, Std.le_refl, List.getElem_append_right, Nat.sub_self, List.getElem_cons_zero])

/-! ### A transact names only a root the pool actually produced -/

/-- One step either leaves tree `tn`'s roots unchanged (a step that inserted into a
    *different* tree) or prepends exactly one new root to it
    (`insertLeaves_rootsAt_shape`, applied to whichever
    batch the constructor inserts) — the structural fact `rootsAt_grounded` needs,
    stated without naming the pushed root's value, since each constructor computes a
    different one. -/
theorem step_rootsAt_shape {s s' : PoolState} (hstep : Step s s') (tn : Nat) :
    s'.rootsAt' tn = s.rootsAt' tn ∨ ∃ r, s'.rootsAt' tn = r :: s.rootsAt' tn := by
  cases hstep with
  | setFeeRatio => exact Or.inl rfl
  | shield token x npk hValue hSpendable =>
    exact insertLeaves_rootsAt_shape s.trees
      [hashCommitment (⟨npk, token, shieldBase s.feeRatio x⟩ : CommitmentPreimage)] tn
  | transact caller w pub bp hN hM hC hBound hAdapt newNotes hOutputs rest spent' records
      openings hRoot hRemove hNullify hRecords =>
    exact insertLeaves_rootsAt_shape s.trees (newNotes.map hashCommitment) tn
  | transactOwned w pub bp hN hM hC caller hCaller hBound hAdapt hNoUnshield rest spent'
      openings hRoot hRemove hNullify =>
    exact insertLeaves_rootsAt_shape s.trees
      ((ownedNewNotes w).map hashCommitment) tn

/-- Every reachable state's tree-`tn` root history is `rootsAt genesisTrees tn` with zero
    or more roots the pool itself pushed to that tree, prepended. -/
theorem rootsAt_grounded {s : PoolState} (h : Reachable s) (tn : Nat) :
    ∃ pushed : List Term, s.rootsAt' tn = pushed ++ rootsAt genesisTrees tn := by
  induction h with
  | genesis _ _ _ => exact ⟨[], rfl⟩
  | step _ hstep ih =>
    obtain ⟨pushed, hpushed⟩ := ih
    rcases step_rootsAt_shape hstep tn with heq | ⟨r, heq⟩
    · exact ⟨pushed, heq.trans hpushed⟩
    · exact ⟨r :: pushed, by rw [heq, hpushed, List.cons_append]⟩

/--
**A transact names only a root the pool actually produced, for the tree it names.**
`rootsAt_grounded` shows `s.rootsAt' tn`, for any reachable `s` and tree `tn`, is built
from `rootsAt genesisTrees tn` by prepending values the pool itself pushed to that tree at
earlier `shield`/`transact`/`transactOwned` steps — never anything else. A
`transact`/`transactOwned`/`shield` step's own `hRoot : pub.merkleRoot ∈ s.rootsAt'
treeNumber` precondition then means the named root is one of those pushed values, or
the genesis root of that tree — never a caller's invention. S-RG, "RAILGUN Core System
& Protocol": "The contract checks to make sure: ... The Merkle root is the current or a
previous Merkle root, to prevent users from making up UTXOs." -/
theorem transact_root_was_produced (s : ReachableState Pool.machine)
    (tn : Nat) {root : Term} (hRoot : root ∈ s.state.rootsAt' tn) :
    root ∈ rootsAt genesisTrees tn ∨
      ∃ pushed : List Term, root ∈ pushed ∧ s.state.rootsAt' tn = pushed ++ rootsAt genesisTrees tn := by
  obtain_reach ⟨s, h : Reachable s⟩ := s
  obtain ⟨pushed, hpushed⟩ := rootsAt_grounded h tn
  rw [hpushed] at hRoot
  rcases List.mem_append.mp hRoot with h1 | h2
  · exact Or.inr ⟨pushed, h1, hpushed⟩
  · exact Or.inl h2

/-! ### Every root of a tree is the root of a prefix of its leaves -/

/-- Every root in a tree's history is `treeRoot` of a prefix of the tree's current leaf
    list. The pool pushes a root only at an insertion (`TreeState.extend`), and an
    insertion only appends leaves. A proof against a historical root therefore opens a
    leaf that the tree still holds (`MerkleProof.opens_treeRoot`). -/
structure RootsOfPrefixes (s : PoolState) : Prop where
  roots : ∀ tn r, r ∈ s.rootsAt' tn → ∃ ls, ls <+: s.leavesAt' tn ∧ r = treeRoot TreeDepth ls

/-- One insertion keeps every root a root of a prefix: the new root is the root of the
    whole new leaf list, and an old prefix stays a prefix of the appended list. -/
theorem insertLeaves_rootsOfPrefixes (trees : List TreeState) (newLeaves : List Term)
    (ih : ∀ tn r, r ∈ rootsAt trees tn → ∃ ls, ls <+: leavesAt trees tn ∧ r = treeRoot TreeDepth ls) :
    ∀ tn r, r ∈ rootsAt (insertLeaves trees newLeaves) tn →
      ∃ ls, ls <+: leavesAt (insertLeaves trees newLeaves) tn ∧ r = treeRoot TreeDepth ls := by
  intro tn r hr
  rw [insertLeaves_rootsAt] at hr
  rw [insertLeaves_leavesAt]
  by_cases h : tn = insertTree trees newLeaves.length
  · rw [if_pos h] at hr
    rw [if_pos h]
    rcases List.mem_cons.mp hr with hr | hr
    · exact ⟨_, List.prefix_refl _, hr⟩
    · obtain ⟨ls, hpre, hls⟩ := ih tn r hr
      exact ⟨ls, hpre.trans (List.prefix_append _ _), hls⟩
  · rw [if_neg h] at hr
    rw [if_neg h]
    exact ih tn r hr

theorem genesis_rootsOfPrefixes (r : FeeRatio) (feeAdmin treasury : Term) :
    RootsOfPrefixes (genesis r feeAdmin treasury) := by
  refine ⟨fun tn root hr => ?_⟩
  cases tn with
  | zero =>
    simp only [genesis, PoolState.rootsAt', rootsAt, genesisTrees, List.getElem?_cons_zero,
      List.mem_singleton] at hr
    exact ⟨[], List.nil_prefix, hr⟩
  | succ n =>
    simp only [genesis, PoolState.rootsAt', rootsAt, genesisTrees, List.getElem?_cons_succ,
      List.getElem?_nil, List.not_mem_nil] at hr

theorem step_preserves_rootsOfPrefixes {s s' : PoolState} (ih : RootsOfPrefixes s)
    (hstep : Step s s') : RootsOfPrefixes s' := by
  cases hstep with
  | setFeeRatio => exact ⟨ih.roots⟩
  | shield => exact ⟨insertLeaves_rootsOfPrefixes s.trees _ ih.roots⟩
  | transact => exact ⟨insertLeaves_rootsOfPrefixes s.trees _ ih.roots⟩
  | transactOwned => exact ⟨insertLeaves_rootsOfPrefixes s.trees _ ih.roots⟩

/-- Every reachable state has every root a root of a prefix of its leaves. -/
theorem roots_of_prefixes (s : ReachableState Pool.machine) : RootsOfPrefixes s.state := by
  obtain_reach ⟨s, h : Reachable s⟩ := s
  induction h with
  | genesis r a b => exact genesis_rootsOfPrefixes r a b
  | step _ hstep ih => exact step_preserves_rootsOfPrefixes ih hstep

/-! ### The preimage registry -/

/-- One step keeps the preimage registry consistent. -/
theorem step_preimageOf_consistent {s s' : PoolState} (hstep : Step s s')
    (h : RegistryConsistent s.preimageOf) : RegistryConsistent s'.preimageOf := by
  cases hstep with
  | setFeeRatio => exact h
  | shield => exact recordStep_preserves_consistency h rfl
  | transact _ _ _ _ _ _ hC _ _ _ _ _ _ _ _ _ _ _ hRecords =>
    exact applyRecords_preserves_consistency h fun cp hcp => transactOutputRecords_valid hC cp (hRecords.subset hcp)
  | transactOwned _ _ _ _ _ hC => exact applyRecords_preserves_consistency h (ownedOutputRecords_valid hC)

/--
**The preimage registry is always consistent.** Every entry the pool has ever written to
`preimageOf`, at any reachable state, hashes to the commitment it is recorded under —
lifting `ArmadaLean.PoolOwned.preimageOf_consistent` from one transaction's batch
(`recordPreimages`) to the pool's whole history (`applyRecords`, at every
`shield`/`transact`/`transactOwned` step).
Source: TransactModule.sol:590-604, ShieldModule.sol:71,136. -/
theorem pool_preimageOf_consistent (s : ReachableState Pool.machine)
    : RegistryConsistent s.state.preimageOf := by
  obtain_reach ⟨s, h : Reachable s⟩ := s
  induction h with
  | genesis _ _ _ => intro c pre hc; (simp? [genesis] at hc says simp only [genesis, reduceCtorEq] at hc)
  | step _ hstep ih => exact step_preimageOf_consistent hstep ih

/--
**After an owned transact, the pool's preimage registry returns exactly this output's
own preimage for its own commitment.** `transactOwned` discloses every output
(`_validatePublicOutputs(requireAll = true)`, TransactModule.sol:630-634), so folding
`ownedOutputRecords w pub` through `applyRecords` writes every one, and
`applyRecords_returns` shows the fold settles exactly there, whatever else the batch
later writes to the same key (never actually different, by `hashCommitment_inj`: two
outputs sharing a commitment must share a preimage). -/
theorem transactOwned_records_all {reg : PreimageRegistry} {N M : Nat}
    {w : TransactOwnedWitness N M} {pub : TransactOwnedPublic N M}
    (hC : OwnedConstrained w pub) (j : Fin M) :
    applyRecords reg (ownedOutputRecords w pub) (pub.commitmentsOut j) =
      some (⟨w.npkOut j, w.token, w.valueOut j⟩ : CommitmentPreimage) := by
  apply applyRecords_returns (ownedOutputRecords_valid hC)
  exact List.mem_ofFn.mpr ⟨j, rfl⟩

/-! ### Can happen -/

/-- Converting a `Fin`-indexed pairwise-distinctness fact (as `ArmadaLean.PoolOwned
    .owned_spend_can_happen` takes it, via `List.ofFn`) into the pointwise form
    `Constrained.distinct` needs. Leaf indices are plain `Nat` tree positions, never
    hashed, so this lemma is unaffected by the symbolic `Term` model. -/
theorem ofFn_pairwise_ne {α : Type} {N : Nat} (f : Fin N → α)
    (h : (List.ofFn f).Pairwise (· ≠ ·)) : ∀ i j : Fin N, i ≠ j → f i ≠ f j := by
  rw [List.pairwise_iff_getElem] at h
  intro i j hij
  rcases Nat.lt_or_gt_of_ne (fun heq => hij (Fin.ext heq)) with hlt | hlt
  · have hh := h i.1 j.1 (by (simp? says simp only [List.length_ofFn, Fin.is_lt])) (by (simp? says simp only [List.length_ofFn, Fin.is_lt])) hlt
    simp only [List.getElem_ofFn] at hh
    (simpa? using hh says simpa only [ne_eq, Fin.eta] using hh)
  · have hh := h j.1 i.1 (by (simp? says simp only [List.length_ofFn, Fin.is_lt])) (by (simp? says simp only [List.length_ofFn, Fin.is_lt])) hlt
    simp only [List.getElem_ofFn] at hh
    intro heq
    exact hh (by (simpa? using heq.symm says simpa only [Fin.eta] using heq.symm))

/-- The converse of `ofFn_pairwise_ne`: a function that maps distinct indices to
    distinct values builds a list with no repetition. -/
theorem ofFn_nodup_of_ne {α : Type} {N : Nat} (f : Fin N → α)
    (h : ∀ i j : Fin N, i ≠ j → f i ≠ f j) : (List.ofFn f).Nodup := by
  rw [List.Nodup, List.pairwise_iff_getElem]
  intro i j hi hj hij
  simp only [List.getElem_ofFn]
  apply h
  intro heq
  have := congrArg Fin.val heq
  simp only at this
  omega

/-- `VerifyAccepts pub` holds iff some Groth16 proof over `pub`'s public inputs makes
    `PrivacyPool.verify` return `true` (PrivacyPool.sol:506-552), when `testingMode` is
    off. Left abstract, exactly as `ArmadaLean.PoolOwned.VerifyOwnedAccepts` is. -/
axiom VerifyAccepts : {N M : Nat} → TransactPublic N M → Prop

/-- Groth16 completeness for the plain circuit, named as an explicit hypothesis exactly
    as `ArmadaLean.PoolOwned.OwnedProofCompleteness` is for the owned circuit: a
    witness/public pair satisfying every `Transact.circom` constraint has an accepted
    proof. -/
structure TransactProofCompleteness where
  complete : ∀ {N M : Nat} {w : TransactWitness N M} {pub : TransactPublic N M},
    Constrained w pub → VerifyAccepts pub

/-- Groth16 knowledge soundness over the deployed verifying key for the plain circuit,
    named as an explicit hypothesis, not a global axiom, exactly as
    `ArmadaLean.PoolOwned.OwnedProofSoundness` is for the owned circuit: every public
    input that the trusted verifier accepts has a witness that satisfies every
    `Transact.circom` constraint. It is the trusted-verifier assumption: the proof
    system itself is sound, so an accepted proof always has a satisfying witness.
    It is the converse of `TransactProofCompleteness`. -/
structure TransactProofSoundness where
  sound : ∀ {N M : Nat} {pub : TransactPublic N M},
    VerifyAccepts pub → ∃ w : TransactWitness N M, Constrained w pub

/-- `verify` (`Pool.Verifier`, `ArmadaLean/Pool.lean`, rule PE3) realizes the model's
    trusted verifier: for each circuit, `verify`'s check accepts some proof over a public
    input exactly when the model's own `VerifyAccepts`/`VerifyOwnedAccepts` does. Restates
    their doc comments with `verify` standing for `PrivacyPool.verify`/`verifyOwned`.
    `Pool.apply` does not take this as a hypothesis; `Pool.apply_shield_equation`,
    `Pool.apply_transact_equation` and `Pool.apply_transactOwned_equation` (rule PE4,
    PE5) do. -/
structure Pool.Verifier.Realizes (verify : Pool.Verifier) : Prop where
  transact : ∀ {N M : Nat} (pub : TransactPublic N M),
    VerifyAccepts pub ↔ ∃ proof, verify.transact pub proof = true
  owned : ∀ {N M : Nat} (pub : TransactOwnedPublic N M),
    VerifyOwnedAccepts pub ↔ ∃ proof, verify.owned pub proof = true

/-- "An honest key holder's signature verifies" — the brief's `can-happen`-only
    assumption, named as an explicit hypothesis: a signer who holds the private key
    behind `pk` can produce, for any message, a signature `EdDSAVerify` accepts.
    `EdDSAVerify` itself is left abstract (`ArmadaLean.Transact`); this structure only
    asserts the forward (signing) direction a real key holder has. The message is a
    `Term` — `msgHashOf`'s output, the circuit's EdDSA message hash. -/
structure HonestSignature where
  sign : (Nat × Nat) → Term → (Nat × Nat × Nat)
  signSound : ∀ pk msg, EdDSAVerify pk (sign pk msg) msg

/--
**Can happen (circuit level): a `Transact` spend by a real key holder, with an accepted
proof, succeeds.** Mirrors `ArmadaLean.PoolOwned.owned_spend_can_happen` exactly, with
the EdDSA signature (`hSig`) replacing owner-field authorization: `publicKey`,
`nullifyingKey`, `randomIn`, `valueIn`, `leavesIndices`, `pathElements`, `npkOut`,
`valueOut` are the real key holder's own data — the witness for `N` notes it genuinely
holds at Merkle root `root`, re-minted into `M` fresh outputs of equal total value.
`transact_spend_can_happen` clears every circuit-level gate this model covers: the
constraints hold (`Constrained`, by construction), `verify` accepts (`hComplete
.complete`), and the nullifiers are fresh so a later `markSpent` call does not revert
(`markSpent_succeeds`, using `distinct_leaves_distinct_nullifiers` to turn the holder's
genuinely-distinct note positions into pairwise-distinct nullifiers, exactly as
`owned_spend_can_happen` does).
Source: Transact.circom:57-186. -/
theorem transact_spend_can_happen {N M : Nat} (hComplete : TransactProofCompleteness)
    (hSig : HonestSignature) (publicKey : Nat × Nat)
    (nullifyingKey : Nat) (token : Token) (boundParamsHash : Term) (root : Term)
    (randomIn valueIn : Fin N → Nat) (leavesIndices : Fin N → Nat)
    (pathElements : Fin N → List (Term × Bool)) (npkOut : Fin M → Term) (valueOut : Fin M → Nat)
    (hMerkle : ∀ i,
      MerkleProof 16
        (commitment (npk (masterPublicKey publicKey nullifyingKey) (randomIn i)) token
          (valueIn i))
        (pathElements i) (leavesIndices i) root)
    (hRangeIn : ∀ i, RangeChecked120 (valueIn i))
    (hRangeOut : ∀ j, RangeChecked120 (valueOut j))
    (hBalance : listSum (List.ofFn valueIn) = listSum (List.ofFn valueOut))
    (hDistinctLeaves : (List.ofFn leavesIndices).Pairwise (· ≠ ·))
    (spent : NullifierSet)
    (hFresh : ∀ i, nullifier (Term.val nullifyingKey) (leavesIndices i) ∉ spent) :
    ∃ (w : TransactWitness N M) (pub : TransactPublic N M),
      Constrained w pub ∧
      VerifyAccepts pub ∧
      (∀ j, hashCommitment ⟨npkOut j, token, valueOut j⟩ = pub.commitmentsOut j) ∧
      ∃ spent', markSpent spent (List.ofFn pub.nullifiers) = some spent' := by
  let pub : TransactPublic N M :=
    { merkleRoot := root, boundParamsHash := boundParamsHash,
      nullifiers := fun i => nullifier (Term.val nullifyingKey) (leavesIndices i),
      commitmentsOut := fun j => commitment (npkOut j) token (valueOut j) }
  let w : TransactWitness N M :=
    { token := token, publicKey := publicKey,
      signature := hSig.sign publicKey (msgHashOf pub), nullifyingKey := nullifyingKey,
      randomIn := randomIn, valueIn := valueIn, pathElements := pathElements,
      leavesIndices := leavesIndices, npkOut := npkOut, valueOut := valueOut }
  have hConstrained : Constrained w pub :=
    { merkle := hMerkle, nullifiers := fun _ => rfl,
      outputs := fun _ => rfl, rangeIn := hRangeIn, rangeOut := hRangeOut,
      balance := congrArg (· % p) hBalance,
      distinct := ofFn_pairwise_ne leavesIndices hDistinctLeaves,
      sig := hSig.signSound publicKey (msgHashOf pub) }
  refine ⟨w, pub, hConstrained, hComplete.complete hConstrained, fun _ => rfl, ?_⟩
  apply markSpent_succeeds
  · have hmap := distinct_leaves_distinct_nullifiers (Term.val nullifyingKey) (List.ofFn leavesIndices)
      hDistinctLeaves
    have heq : (List.ofFn leavesIndices).map (nullifier (Term.val nullifyingKey))
        = List.ofFn (fun i => nullifier (Term.val nullifyingKey) (leavesIndices i)) := List.map_ofFn
    rwa [heq] at hmap
  · intro n hn
    obtain ⟨i, hi⟩ := List.mem_ofFn.mp hn
    rw [← hi]
    exact hFresh i

/-- **Can happen: a shield succeeds.** Any positive gross amount `x` whose note value
    `shieldBase s.feeRatio x` is spendable creates a note (`shield_creates_exactly`). The
    positivity check is on the gross amount (`_validateCommitmentPreimage`,
    ShieldModule.sol:244). No proof, no honest-prover assumption: shield carries no
    SNARK. No pause and no capacity gate: a full tree rolls over to a new one. -/
theorem shield_can_happen (s : ReachableState Pool.machine) (token : Token)
    (x : Nat) (npk : Term)
    (hValue : 0 < x) (hSpendable : Spendable (shieldBase s.state.feeRatio x)) :
    ∃ s', Step s.state s' := obtain_reach% ⟨s, _hr⟩ := s;
  let H := shield_creates_exactly token x npk hValue hSpendable; ⟨H.choose, H.choose_spec.1⟩

/-- **Can happen: the fee admin changes the fee rate.** From every reachable state, the
    fee admin's setter call with any rate `r` is a step to a state with fee rate `r`
    (design decision 2026-11-06, item (d)). The one check is the caller: the fee admin
    `s.feeAdmin` passes it. -/
theorem setFeeRatio_can_happen (s : ReachableState Pool.machine) (r : FeeRatio) :
    ∃ s', Step s.state s' ∧ s'.feeRatio = r :=
  ⟨_, .setFeeRatio s.state.feeAdmin rfl r, rfl⟩

/-- **Can happen: a transact (private transfer, no unshield) succeeds.** A real key
    holder with `N` live notes in tree `bp.treeNumber`, re-minting them into `M` new
    notes of equal total value, clears every check of `Step.transact`: the witness is
    built and shown `Constrained` as `transact_spend_can_happen` builds one,
    `hComplete.complete` shows `verify` accepts, and `markSpent_succeeds` (with
    `distinct_leaves_distinct_nullifiers`) shows the nullifiers are fresh. `bp` is the
    transaction's bound parameters, with no unshield (`hNoUnshield`) and an adapt
    contract, if any, equal to `caller` (`hAdapt`). `hLive` is the ghost liveness
    precondition, keyed by the `(treeNumber, leaf position)` pairs of the notes.
    Source: TransactModule.sol:43-96. -/
theorem transact_can_happen (s : ReachableState Pool.machine)
    (hComplete : TransactProofCompleteness)
    (hSig : HonestSignature) {N M : Nat} (caller : Term) (bp : BoundParams)
    (hAdapt : AdaptAllows bp caller) (hNoUnshield : bp.unshield = none)
    (publicKey : Nat × Nat) (nullifyingKey : Nat) (token : Token) (root : Term)
    (randomIn valueIn : Fin N → Nat) (leavesIndices : Fin N → Nat)
    (pathElements : Fin N → List (Term × Bool)) (npkOut : Fin M → Term) (valueOut : Fin M → Nat)
    (hN : N ≤ 8) (hM : M ≤ 4)
    (hRoot : root ∈ s.state.rootsAt' bp.treeNumber)
    (hMerkle : ∀ i,
      MerkleProof 16
        (commitment (npk (masterPublicKey publicKey nullifyingKey) (randomIn i)) token
          (valueIn i))
        (pathElements i) (leavesIndices i) root)
    (hRangeIn : ∀ i, RangeChecked120 (valueIn i))
    (hRangeOut : ∀ j, RangeChecked120 (valueOut j))
    (hBalance : listSum (List.ofFn valueIn) = listSum (List.ofFn valueOut))
    (hDistinctLeaves : (List.ofFn leavesIndices).Pairwise (· ≠ ·))
    (hFresh : ∀ i, nullifier (Term.val nullifyingKey) (leavesIndices i) ∉ s.state.spent bp.treeNumber)
    {rest : List ((Nat × Nat) × CommitmentPreimage)}
    (hLive : removeAll (s.state.live token)
        (List.ofFn fun i =>
          ((bp.treeNumber, leavesIndices i),
            (⟨npk (masterPublicKey publicKey nullifyingKey) (randomIn i), token, valueIn i⟩ :
              CommitmentPreimage)))
        = some rest) :
    ∃ s', Step s.state s' := by
  obtain_reach ⟨s, _hr⟩ := s
  let pub : TransactPublic N M :=
    { merkleRoot := root, boundParamsHash := hashBoundParams bp,
      nullifiers := fun i => nullifier (Term.val nullifyingKey) (leavesIndices i),
      commitmentsOut := fun j => commitment (npkOut j) token (valueOut j) }
  let w : TransactWitness N M :=
    { token := token, publicKey := publicKey,
      signature := hSig.sign publicKey (msgHashOf pub), nullifyingKey := nullifyingKey,
      randomIn := randomIn, valueIn := valueIn, pathElements := pathElements,
      leavesIndices := leavesIndices, npkOut := npkOut, valueOut := valueOut }
  have hConstrained : Constrained w pub :=
    { merkle := hMerkle, nullifiers := fun _ => rfl,
      outputs := fun _ => rfl, rangeIn := hRangeIn, rangeOut := hRangeOut,
      balance := congrArg (· % p) hBalance,
      distinct := ofFn_pairwise_ne leavesIndices hDistinctLeaves,
      sig := hSig.signSound publicKey (msgHashOf pub) }
  obtain ⟨spent', hNullify⟩ :
      ∃ spent', markSpent (s.spent bp.treeNumber) (List.ofFn pub.nullifiers) = some spent' := by
    apply markSpent_succeeds
    · have hmap := distinct_leaves_distinct_nullifiers (Term.val nullifyingKey)
        (List.ofFn leavesIndices) hDistinctLeaves
      have heq : (List.ofFn leavesIndices).map (nullifier (Term.val nullifyingKey))
          = List.ofFn pub.nullifiers := List.map_ofFn
      rwa [heq] at hmap
    · intro n hn
      obtain ⟨i, hi⟩ := List.mem_ofFn.mp hn
      rw [← hi]
      exact hFresh i
  have hUnshieldRefines : UnshieldRefines w bp.unshield (transactAllOutputs w) := by
    rw [hNoUnshield]; rfl
  exact ⟨_, Step.transact caller w pub bp hN hM hConstrained rfl hAdapt
    (transactAllOutputs w) hUnshieldRefines rest spent' (transactOutputRecords w pub) []
    hRoot hLive hNullify (List.Sublist.refl _)⟩

/-- **Can happen: an unshield succeeds and pays its recipient.** A real key holder spends
    `N` live notes in tree `bp.treeNumber`; the bound parameters carry the unshield
    `⟨recipient, value⟩` (`hU`), and the circuit's one output is the unshield note
    (`UnshieldRefines`: `npk := recipient`). The step exists, and its payout record gains
    exactly `⟨token, recipient, value⟩`. `_validateTransaction`'s unshield checks
    (TransactModule.sol:295-331; Zokyo 2022-12-21 finding #1) bind the payout to the
    proof. -/
theorem unshield_can_happen (s : ReachableState Pool.machine)
    (hComplete : TransactProofCompleteness)
    (hSig : HonestSignature) {N : Nat} (caller : Term) (bp : BoundParams)
    (hAdapt : AdaptAllows bp caller) (recipient : Term) (value : Nat)
    (hU : bp.unshield = some ⟨recipient, value⟩)
    (publicKey : Nat × Nat) (nullifyingKey : Nat) (token : Token) (root : Term)
    (randomIn valueIn : Fin N → Nat) (leavesIndices : Fin N → Nat)
    (pathElements : Fin N → List (Term × Bool))
    (hN : N ≤ 8)
    (hRoot : root ∈ s.state.rootsAt' bp.treeNumber)
    (hMerkle : ∀ i,
      MerkleProof 16
        (commitment (npk (masterPublicKey publicKey nullifyingKey) (randomIn i)) token
          (valueIn i))
        (pathElements i) (leavesIndices i) root)
    (hRangeIn : ∀ i, RangeChecked120 (valueIn i)) (hRangeOut : RangeChecked120 value)
    (hBalance : listSum (List.ofFn valueIn) = value)
    (hDistinctLeaves : (List.ofFn leavesIndices).Pairwise (· ≠ ·))
    (hFresh : ∀ i, nullifier (Term.val nullifyingKey) (leavesIndices i) ∉ s.state.spent bp.treeNumber)
    {rest : List ((Nat × Nat) × CommitmentPreimage)}
    (hLive : removeAll (s.state.live token)
        (List.ofFn fun i =>
          ((bp.treeNumber, leavesIndices i),
            (⟨npk (masterPublicKey publicKey nullifyingKey) (randomIn i), token, valueIn i⟩ :
              CommitmentPreimage)))
        = some rest) :
    ∃ s', Step s.state s' ∧ s'.payouts = s.state.payouts ++ [⟨token, recipient, value⟩] := by
  obtain_reach ⟨s, _hr⟩ := s
  let pub : TransactPublic N 1 :=
    { merkleRoot := root, boundParamsHash := hashBoundParams bp,
      nullifiers := fun i => nullifier (Term.val nullifyingKey) (leavesIndices i),
      commitmentsOut := fun _ => commitment recipient token value }
  let w : TransactWitness N 1 :=
    { token := token, publicKey := publicKey,
      signature := hSig.sign publicKey (msgHashOf pub), nullifyingKey := nullifyingKey,
      randomIn := randomIn, valueIn := valueIn, pathElements := pathElements,
      leavesIndices := leavesIndices, npkOut := fun _ => recipient, valueOut := fun _ => value }
  have hBalance' : listSum (List.ofFn valueIn) = listSum (List.ofFn w.valueOut) := by
    show listSum (List.ofFn valueIn) = listSum (List.ofFn (fun _ : Fin 1 => value))
    (simp? [List.ofFn_succ, List.ofFn_zero, listSum, hBalance] says simp only [hBalance, List.ofFn_succ, List.ofFn_zero, listSum, Nat.add_zero])
  have hConstrained : Constrained w pub :=
    { merkle := hMerkle, nullifiers := fun _ => rfl,
      outputs := fun _ => rfl, rangeIn := hRangeIn, rangeOut := fun _ => hRangeOut,
      balance := congrArg (· % p) hBalance',
      distinct := ofFn_pairwise_ne leavesIndices hDistinctLeaves,
      sig := hSig.signSound publicKey (msgHashOf pub) }
  obtain ⟨spent', hNullify⟩ :
      ∃ spent', markSpent (s.spent bp.treeNumber) (List.ofFn pub.nullifiers) = some spent' := by
    apply markSpent_succeeds
    · have hmap := distinct_leaves_distinct_nullifiers (Term.val nullifyingKey)
        (List.ofFn leavesIndices) hDistinctLeaves
      have heq : (List.ofFn leavesIndices).map (nullifier (Term.val nullifyingKey))
          = List.ofFn pub.nullifiers := List.map_ofFn
      rwa [heq] at hmap
    · intro n hn
      obtain ⟨i, hi⟩ := List.mem_ofFn.mp hn
      rw [← hi]
      exact hFresh i
  have hUnshieldRefines : UnshieldRefines w bp.unshield ([] : List CommitmentPreimage) := by
    rw [hU]
    show transactAllOutputs w = [] ++ [⟨recipient, w.token, value⟩]
    (simp? [transactAllOutputs, List.ofFn_succ, List.ofFn_zero, w] says simp only [transactAllOutputs, List.ofFn_succ, List.ofFn_zero, List.nil_append, w])
  refine ⟨_, Step.transact caller w pub bp hN (by decide) hConstrained rfl hAdapt
    [] hUnshieldRefines rest spent' (transactOutputRecords w pub) []
    hRoot hLive hNullify (List.Sublist.refl _), ?_⟩
  (simp? [hU, w] says simp only [hU, Option.map_some, Option.toList_some, w])

/-- **Can happen: an owned transact succeeds.** Wires an owned witness, built as
    `ArmadaLean.PoolOwned.owned_spend_can_happen` builds one, into
    `Step.transactOwned`: `hLive` is the ghost liveness precondition, `hN`/`hM` the
    registered-shape bound, the caller `Term.val owner` the authorization check
    (`transactOwned_spends_only_owned` is the matching safety theorem), and `bp` the
    bound parameters (no unshield, adapt contract the owner or none). An owned transact
    can pay out to any recipient's note key; the step publishes no opening
    (`openings := []`).
    Source: TransactModule.sol:488-519 (pool symbolic types approval). -/
theorem owned_transact_can_happen (s : ReachableState Pool.machine)
    (hComplete : OwnedProofCompleteness)
    {N M : Nat} (owner : Address) (token : Token) (bp : BoundParams)
    (hNoUnshield : bp.unshield = none) (root : Term)
    (randomIn valueIn : Fin N → Nat) (leavesIndices : Fin N → Nat)
    (pathElements : Fin N → List (Term × Bool)) (npkOut : Fin M → Term) (valueOut : Fin M → Nat)
    (hN : N ≤ 8) (hM : M ≤ 4)
    (hRoot : root ∈ s.state.rootsAt' bp.treeNumber)
    (hMerkle : ∀ i,
      MerkleProof 16 (commitment (npk (Term.val owner) (randomIn i)) token (valueIn i))
        (pathElements i) (leavesIndices i) root)
    (hRangeIn : ∀ i, RangeChecked120 (valueIn i))
    (hRangeOut : ∀ j, RangeChecked120 (valueOut j))
    (hBalance : listSum (List.ofFn valueIn) = listSum (List.ofFn valueOut))
    (hDistinctLeaves : (List.ofFn leavesIndices).Pairwise (· ≠ ·))
    (hFresh : ∀ i, nullifier (Term.val owner) (leavesIndices i) ∉ s.state.spent bp.treeNumber)
    (hAdapt : AdaptAllows bp (Term.val owner))
    {rest : List ((Nat × Nat) × CommitmentPreimage)}
    (hLive : removeAll (s.state.live token)
        (List.ofFn fun i =>
          ((bp.treeNumber, leavesIndices i),
            (⟨npk (Term.val owner) (randomIn i), token, valueIn i⟩ : CommitmentPreimage)))
        = some rest) :
    ∃ s', Step s.state s' := by
  obtain_reach ⟨s, _hr⟩ := s
  let pub : TransactOwnedPublic N M :=
    { merkleRoot := root, boundParamsHash := hashBoundParams bp,
      nullifiers := fun i => nullifier (Term.val owner) (leavesIndices i),
      commitmentsOut := fun j => commitment (npkOut j) token (valueOut j),
      owner := owner }
  let w : TransactOwnedWitness N M :=
    { token := token, randomIn := randomIn, valueIn := valueIn, pathElements := pathElements,
      leavesIndices := leavesIndices, npkOut := npkOut, valueOut := valueOut }
  have hConstrained : OwnedConstrained w pub :=
    { merkle := hMerkle, nullifiers := fun _ => rfl,
      outputs := fun _ => rfl, rangeIn := hRangeIn, rangeOut := hRangeOut,
      balance := congrArg (· % p) hBalance }
  obtain ⟨spent', hNullify⟩ :
      ∃ spent', markSpent (s.spent bp.treeNumber) (List.ofFn pub.nullifiers) = some spent' := by
    apply markSpent_succeeds
    · have hmap := distinct_leaves_distinct_nullifiers (Term.val owner)
        (List.ofFn leavesIndices) hDistinctLeaves
      have heq : (List.ofFn leavesIndices).map (nullifier (Term.val owner))
          = List.ofFn pub.nullifiers := List.map_ofFn
      rwa [heq] at hmap
    · intro n hn
      obtain ⟨i, hi⟩ := List.mem_ofFn.mp hn
      rw [← hi]
      exact hFresh i
  exact ⟨_, Step.transactOwned w pub bp hN hM hConstrained (Term.val owner) rfl rfl hAdapt
    hNoUnshield rest spent' [] hRoot hLive hNullify⟩

/-! ### Every inserted leaf has a Merkle witness to a root the pool produced -/

/-- One step either leaves tree `tn`'s leaves and roots both unchanged, or appends to
    `leavesAt' tn` and pushes exactly `ArmadaLean.Merkle.treeRoot TreeDepth` of the
    result to `rootsAt' tn` — `insertLeaves_rootsAt_matches_leavesAt`, applied to
    whichever batch and tree a `Step` constructor targets. A standalone wrapper
    (states inferred from `hstep`, as `step_rootsAt_shape` already is) so
    `reachable_rootAt_matches_leavesAt`'s induction never needs to name the previous
    state by hand. -/
theorem step_leavesAt_rootsAt_matches {s s' : PoolState} (hstep : Step s s') (tn : Nat) :
    (s'.leavesAt' tn = s.leavesAt' tn ∧ s'.rootsAt' tn = s.rootsAt' tn) ∨
      s'.rootsAt' tn = treeRoot TreeDepth (s'.leavesAt' tn) :: s.rootsAt' tn := by
  cases hstep with
  | setFeeRatio => exact Or.inl ⟨rfl, rfl⟩
  | shield token x npk hValue hSpendable =>
    exact insertLeaves_rootsAt_matches_leavesAt s.trees
      [hashCommitment (⟨npk, token, shieldBase s.feeRatio x⟩ : CommitmentPreimage)] tn
  | transact caller w pub bp hN hM hC hBound hAdapt newNotes hOutputs rest spent' records
      openings hRoot hRemove hNullify hRecords =>
    exact insertLeaves_rootsAt_matches_leavesAt s.trees
      (newNotes.map hashCommitment) tn
  | transactOwned w pub bp hN hM hC caller hCaller hBound hAdapt hNoUnshield rest spent'
      openings hRoot hRemove hNullify =>
    exact insertLeaves_rootsAt_matches_leavesAt s.trees
      ((ownedNewNotes w).map hashCommitment) tn

/-- **The root most recently pushed to a tree always matches that tree's actual leaf
    list — for every tree the pool has actually inserted a leaf into.** Every
    reachable state's tree-`tn` head root is `ArmadaLean.Merkle.treeRoot TreeDepth` of
    its own `leavesAt' tn` — never a free choice (`step_leavesAt_rootsAt_matches`),
    proved by induction on `Reachable`. Stated as a disjunction with "tree `tn` has no
    leaves at all" to cover a tree number no step has reached yet (a tree that does not
    exist has no leaves, `leavesAt`) — `leaf_has_merkle_witness` rules that case out
    directly via its own leaf hypothesis. -/
theorem reachable_rootAt_matches_leavesAt {s : PoolState} (h : Reachable s) (tn : Nat) :
    s.leavesAt' tn = [] ∨ treeRoot TreeDepth (s.leavesAt' tn) ∈ s.rootsAt' tn := by
  induction h with
  | genesis _ _ _ =>
    left; cases tn <;> simp [genesis, genesisTrees, PoolState.leavesAt', leavesAt]
  | step _ hstep ih =>
    rcases step_leavesAt_rootsAt_matches hstep tn with ⟨hl, hr⟩ | hr
    · rw [hl, hr]; exact ih
    · right; rw [hr]; exact List.mem_cons_self

/-- One step's new batch is always within capacity (`1` for a shield, `≤ M ≤ 4` for a
    transact/transactOwned), so `insertLeaves_leavesAt_capacity` keeps every tree
    within capacity across the step, given it held before. A standalone wrapper
    (states inferred from `hstep`) so `reachable_leavesAt_capacity`'s induction never
    needs to name the previous state by hand. -/
theorem step_leavesAt_capacity_preserved {s s' : PoolState} (hstep : Step s s')
    (hOldCap : ∀ k, (s.leavesAt' k).length ≤ 2 ^ TreeDepth) (tn : Nat) :
    (s'.leavesAt' tn).length ≤ 2 ^ TreeDepth := by
  cases hstep with
  | setFeeRatio => exact hOldCap tn
  | shield token x npk hValue hSpendable =>
    exact insertLeaves_leavesAt_capacity s.trees
      [hashCommitment (⟨npk, token, shieldBase s.feeRatio x⟩ : CommitmentPreimage)] tn
      (by (simp? says simp only [List.length_cons, List.length_nil, Nat.zero_add]); unfold TreeDepth; omega) hOldCap
  | transact caller w pub bp hN hM hC hBound hAdapt newNotes hOutputs rest spent' records
      openings hRoot hRemove hNullify hRecords =>
    have hlen : newNotes.length ≤ 4 := Nat.le_trans (unshieldRefines_length_le hOutputs) hM
    exact insertLeaves_leavesAt_capacity s.trees
      (newNotes.map hashCommitment) tn (by (simp? says simp only [List.length_map]); unfold TreeDepth; omega) hOldCap
  | transactOwned w pub bp hN hM hC caller hCaller hBound hAdapt hNoUnshield rest spent'
      openings hRoot hRemove hNullify =>
    have hlen : (ownedNewNotes w).length ≤ 4 := by
      unfold ownedNewNotes
      simp only [List.length_ofFn]
      omega
    exact insertLeaves_leavesAt_capacity s.trees
      ((ownedNewNotes w).map hashCommitment) tn (by (simp? says simp only [List.length_map]); unfold TreeDepth; omega) hOldCap

/-- **No tree's leaf list ever exceeds its own capacity.** Every reachable state's
    `leavesAt' tn` has at most `2 ^ TreeDepth` entries, for every tree `tn` — no
    capacity hypothesis gates any `Step` constructor any more (the rollover
    departure, module comment); instead, each inserted batch is at most `4` notes
    (`M ≤ 4`, or `1` for a shield), always within `2 ^ TreeDepth = 2 ^ 16`, and
    `step_leavesAt_capacity_preserved` shows a within-capacity batch keeps every tree
    within capacity, including a freshly-rolled-into one. -/
theorem reachable_leavesAt_capacity {s : PoolState} (h : Reachable s) :
    ∀ tn, (s.leavesAt' tn).length ≤ 2 ^ TreeDepth := by
  induction h with
  | genesis _ _ _ =>
    intro tn
    cases tn <;> simp [genesis, genesisTrees, PoolState.leavesAt', leavesAt]
  | step _ hstep ih =>
    exact step_leavesAt_capacity_preserved hstep ih

/--
**Every leaf the pool has ever inserted into a tree has a real Merkle witness to a
root the pool produced for that tree.** For any reachable state `s`, tree `tn` and
position `i` that holds a leaf `leaf`, the path `ArmadaLean.Merkle.treePath TreeDepth
(s.leavesAt' tn) i` is a genuine membership proof: folding it from `leaf` reconstructs
`treeRoot TreeDepth (s.leavesAt' tn)` (`treePath_correct_of_getElem?`,
`reachable_leavesAt_capacity` for the depth bound), and that root is one of the pool's
own, `s.rootsAt' tn` (`reachable_rootAt_matches_leavesAt`). `rootsAt' tn` never expires
an entry (`PrivacyPoolStorage.rootHistory`, PrivacyPoolStorage.sol:171), so the witness
built from the latest leaf list verifies against a root the contract still accepts.
The leaf is an `Option` lookup, not a lookup with a default value (finding P-8). -/
theorem leaf_has_merkle_witness (s : ReachableState Pool.machine) (tn : Nat)
    {i : Nat} {leaf : Term} (hleaf : (s.state.leavesAt' tn)[i]? = some leaf) :
    merkleRoot leaf (treePath TreeDepth (s.state.leavesAt' tn) i) =
        treeRoot TreeDepth (s.state.leavesAt' tn) ∧
      treeRoot TreeDepth (s.state.leavesAt' tn) ∈ s.state.rootsAt' tn := by
  obtain_reach ⟨s, h : Reachable s⟩ := s
  obtain ⟨hi, _⟩ := List.getElem?_eq_some_iff.mp hleaf
  have hcap := reachable_leavesAt_capacity h tn
  have hilt : i < 2 ^ TreeDepth := Nat.lt_of_lt_of_le hi hcap
  refine ⟨treePath_correct_of_getElem? TreeDepth (s.leavesAt' tn) i hilt hleaf, ?_⟩
  rcases reachable_rootAt_matches_leavesAt h tn with hnil | hmem
  · rw [hnil] at hleaf; (simp? at hleaf says simp only [List.length_nil, Nat.not_lt_zero, not_false_eq_true, getElem?_neg, reduceCtorEq] at hleaf)
  · exact hmem

/-! ### A leaf, once inserted, never moves

The pool's Merkle tree is append-only. `MerkleModule` is an "Append-only incremental
binary Merkle tree over Poseidon" (MerkleModule.sol:12). `insertLeaves`
(MerkleModule.sol:54-121) writes new leaves at `nextLeafIndex` and later positions only,
and no function removes or rewrites a leaf. The Railgun whitepaper (S-RG, "RAILGUN
Core System & Protocol") keeps the notes in "batch incremental Merkle trees", and "The
hashes of the output UTXOs are then added to the Merkle tree so they can be spent in
the future." -/

/-- One step either leaves tree `tn`'s leaves unchanged or appends to them
    (`insertLeaves_leavesAt_length_ge`, `insertLeaves_leavesAt`), applied to whichever
    batch and tree a `Step` constructor inserts. A position in range stays in range and
    keeps its leaf. -/
theorem step_leavesAt_stable {s s' : PoolState} (hstep : Step s s') (tn pos : Nat)
    (hpos : pos < (s.leavesAt' tn).length) :
    pos < (s'.leavesAt' tn).length ∧ (s'.leavesAt' tn)[pos]? = (s.leavesAt' tn)[pos]? := by
  have key : ∀ newLeaves : List Term,
      pos < (leavesAt (insertLeaves s.trees newLeaves) tn).length ∧
        (leavesAt (insertLeaves s.trees newLeaves) tn)[pos]? = (leavesAt s.trees tn)[pos]? := by
    intro newLeaves
    have hpos' : pos < (leavesAt s.trees tn).length := hpos
    refine ⟨Nat.lt_of_lt_of_le hpos' (insertLeaves_leavesAt_length_ge s.trees newLeaves tn), ?_⟩
    rw [insertLeaves_leavesAt]
    by_cases h : tn = insertTree s.trees newLeaves.length
    · rw [if_pos h, List.getElem?_append_left hpos']
    · rw [if_neg h]
  cases hstep with
  | setFeeRatio => exact ⟨hpos, rfl⟩
  | shield token x npk hValue hSpendable => exact key _
  | transact caller w pub bp hN hM hC hBound hAdapt newNotes hOutputs rest spent' records
      openings hRoot hRemove hNullify hRecords => exact key _
  | transactOwned w pub bp hN hM hC caller hCaller hBound hAdapt hNoUnshield rest spent'
      openings hRoot hRemove hNullify => exact key _

/--
**A leaf, once inserted at a position, never changes in any later reachable state.**
For any `ReachableFrom s s'` and any position in range at `s`
(`pos < (s.leavesAt' tn).length`), the position stays in range at `s'` and holds the same
leaf. The tree is append-only (section comment: MerkleModule.sol:12, :54-121; S-RG,
"batch incremental Merkle trees"). Proved by induction on `ReachableFrom` with
`step_leavesAt_stable`. The lookup is an `Option`, not a lookup with a default value
(finding P-8). -/
theorem leaf_stable {s s' : PoolState} (h : ReachableFrom s s') (tn pos : Nat)
    (hpos : pos < (s.leavesAt' tn).length) :
    pos < (s'.leavesAt' tn).length ∧ (s'.leavesAt' tn)[pos]? = (s.leavesAt' tn)[pos]? := by
  induction h with
  | refl => exact ⟨hpos, rfl⟩
  | step _ hstep ih =>
    obtain ⟨ihlen, iheq⟩ := ih
    obtain ⟨hlen2, heq2⟩ := step_leavesAt_stable hstep tn pos ihlen
    exact ⟨hlen2, heq2.trans iheq⟩

/-! ### A live owned note with a published opening has a constructible spend witness -/

/--
**A contract-owned note with a recorded preimage and a published opening has a
constructible `OwnedConstrained` spend witness, built entirely from public data.** Given
`N` input notes whose preimages (`preimages`, what `PoolState.preimageOf` records for
every disclosed output, PrivacyPoolStorage.sol:248) sit at known positions of a leaf
list `leaves` (`hLeafValue`; callers instantiate `leaves := s.leavesAt' tn`), and whose
openings `(Term.val owner, r)` appear in a list of published openings (`hOwned`; callers
instantiate `published := s.published`, decision 11) and match the note's `npk`, a
satisfying `OwnedConstrained` witness/public pair exists. Its Merkle path is
`treePath TreeDepth leaves`, computed, not chosen. The pool does not check a published
opening; `hOwned` is the reader's own check against `npk`. -/
theorem owned_spend_witness_exists {N M : Nat}
    (owner : Address) (token : Token) (boundParamsHash : Term)
    (preimages : Fin N → CommitmentPreimage)
    (leavesIndices : Fin N → Nat) (leaves : List Term)
    (published : List (Term × OwnedOpening))
    (hToken : ∀ i, (preimages i).token = token)
    (hOwned : ∀ i, ∃ r, (hashCommitment (preimages i), ⟨Term.val owner, r⟩) ∈ published ∧
      npk (Term.val owner) r = (preimages i).npk)
    (hLeafIndex : ∀ i, leavesIndices i < 2 ^ TreeDepth)
    (hLeafValue : ∀ i, leaves[leavesIndices i]? = some (hashCommitment (preimages i)))
    (npkOut : Fin M → Term) (valueOut : Fin M → Nat)
    (hRangeIn : ∀ i, RangeChecked120 (preimages i).value)
    (hRangeOut : ∀ j, RangeChecked120 (valueOut j))
    (hBalance : listSum (List.ofFn fun i => (preimages i).value) = listSum (List.ofFn valueOut)) :
    ∃ (w : TransactOwnedWitness N M) (pub : TransactOwnedPublic N M),
      OwnedConstrained w pub ∧
      pub.merkleRoot = treeRoot TreeDepth leaves ∧
      pub.boundParamsHash = boundParamsHash ∧
      pub.owner = owner ∧
      w.token = token ∧
      (∀ i, w.valueIn i = (preimages i).value) := by
  let r : Fin N → Nat := fun i => (hOwned i).choose
  let pub : TransactOwnedPublic N M :=
    { merkleRoot := treeRoot TreeDepth leaves, boundParamsHash := boundParamsHash,
      nullifiers := fun i => nullifier (Term.val owner) (leavesIndices i),
      commitmentsOut := fun j => commitment (npkOut j) token (valueOut j),
      owner := owner }
  let w : TransactOwnedWitness N M :=
    { token := token, randomIn := r,
      valueIn := fun i => (preimages i).value,
      pathElements := fun i => treePath TreeDepth leaves (leavesIndices i),
      leavesIndices := leavesIndices, npkOut := npkOut, valueOut := valueOut }
  have hConstrained : OwnedConstrained w pub :=
    { merkle := fun i => by
        have hr := (hOwned i).choose_spec
        have hge : leaves[leavesIndices i]? =
            some (commitment (npk (Term.val owner) (r i)) token ((preimages i).value)) := by
          rw [hr.2, ← hToken i]
          exact hLeafValue i
        exact treePath_merkleProof TreeDepth leaves (leavesIndices i) (hLeafIndex i) hge,
      nullifiers := fun _ => rfl,
      outputs := fun _ => rfl,
      rangeIn := hRangeIn,
      rangeOut := hRangeOut,
      balance := congrArg (· % p) hBalance }
  exact ⟨w, pub, hConstrained, rfl, rfl, rfl, rfl, fun _ => rfl⟩

/-! ### A leaf's nullifier is unspent while it is live -/

/-- Ghost-state invariant bundling five facts needed for `live_note_unspent`, proved
    together since each step case's proof of one leans on the others (at the state
    *before* the step). PART2 is cross-token: a `(treeNumber, position)` key names one
    leaf, hence at most one live entry overall, not merely one per token (a leaf has
    one commitment, hence one token, never two). -/
def LiveSpentInvariant (s : PoolState) : Prop :=
  (∀ t tn pos pre, ((tn, pos), pre) ∈ s.live t → pos < (s.leavesAt' tn).length) ∧
  (∀ t t' tn pos pre pre', ((tn, pos), pre) ∈ s.live t → ((tn, pos), pre') ∈ s.live t' →
    t = t' ∧ pre = pre') ∧
  (∀ tn pos nk, nullifier nk pos ∈ s.spent tn → pos < (s.leavesAt' tn).length) ∧
  (∀ t tn pos pre, ((tn, pos), pre) ∈ s.live t → ∀ nk, nullifier nk pos ∉ s.spent tn) ∧
  (∀ t, (s.live t).Nodup)

theorem genesis_live_spent_invariant (r : FeeRatio) (feeAdmin treasury : Term) :
    LiveSpentInvariant (genesis r feeAdmin treasury) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> intro <;> simp [genesis]

theorem step_preserves_live_spent_invariant {s s' : PoolState} (ih : LiveSpentInvariant s)
    (hstep : Step s s') : LiveSpentInvariant s' := by
  obtain ⟨ih1, ih2, ih3, ih4, ih5⟩ := ih
  simp only [PoolState.leavesAt'] at ih1 ih3
  cases hstep with
  | setFeeRatio => exact ⟨ih1, ih2, ih3, ih4, ih5⟩
  | shield token x npk hValue hSpendable =>
    have hpos0eq := insertStart_eq s.trees 1
    have hlenge := fun tn => insertLeaves_leavesAt_length_ge s.trees
      [hashCommitment (⟨npk, token, shieldBase s.feeRatio x⟩ : CommitmentPreimage)] tn
    have htarget := insertLeaves_target_length s.trees
      [hashCommitment (⟨npk, token, shieldBase s.feeRatio x⟩ : CommitmentPreimage)]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> dsimp only [PoolState.leavesAt']
    · intro t tn pos pre hmem
      by_cases ht : t = token
      · subst t
        simp only at hmem
        rcases List.eq_or_mem_of_mem_cons hmem with heq | hmem
        · injection heq with h1 h2
          injection h1 with h1a h1b
          rw [h1a, h1b]
          simp only [List.length_singleton] at htarget
          omega
        · have hlt := ih1 token tn pos pre hmem
          have hle := hlenge tn
          omega
      · simp only [if_neg ht] at hmem
        have hlt := ih1 t tn pos pre hmem
        have hle := hlenge tn
        omega
    · intro t t' tn pos pre pre' hmem hmem'
      by_cases ht : t = token <;> by_cases ht' : t' = token
      · subst t; subst t'
        simp only at hmem hmem'
        rcases List.eq_or_mem_of_mem_cons hmem with heq | hmem <;>
          rcases List.eq_or_mem_of_mem_cons hmem' with heq' | hmem'
        · exact ⟨rfl, (congrArg Prod.snd heq).trans (congrArg Prod.snd heq').symm⟩
        · exfalso
          injection heq with h1 _
          injection h1 with h1a h1b
          have hlt := ih1 token tn pos pre' hmem'
          rw [h1a, h1b, ← hpos0eq] at hlt
          omega
        · exfalso
          injection heq' with h1 _
          injection h1 with h1a h1b
          have hlt := ih1 token tn pos pre hmem
          rw [h1a, h1b, ← hpos0eq] at hlt
          omega
        · exact ih2 token token tn pos pre pre' hmem hmem'
      · subst t
        simp only at hmem
        simp only [if_neg ht'] at hmem'
        rcases List.eq_or_mem_of_mem_cons hmem with heq | hmem
        · exfalso
          injection heq with h1 _
          injection h1 with h1a h1b
          have hlt := ih1 t' tn pos pre' hmem'
          rw [h1a, h1b, ← hpos0eq] at hlt
          omega
        · exact ih2 token t' tn pos pre pre' hmem hmem'
      · subst t'
        simp only at hmem'
        simp only [if_neg ht] at hmem
        rcases List.eq_or_mem_of_mem_cons hmem' with heq' | hmem'
        · exfalso
          injection heq' with h1 _
          injection h1 with h1a h1b
          have hlt := ih1 t tn pos pre hmem
          rw [h1a, h1b, ← hpos0eq] at hlt
          omega
        · exact ih2 t token tn pos pre pre' hmem hmem'
      · simp only [if_neg ht] at hmem
        simp only [if_neg ht'] at hmem'
        exact ih2 t t' tn pos pre pre' hmem hmem'
    · intro tn pos nk hmem
      have hlt := ih3 tn pos nk hmem
      have hle := hlenge tn
      omega
    · intro t tn pos pre hmem nk
      by_cases ht : t = token
      · subst t
        simp only at hmem
        rcases List.eq_or_mem_of_mem_cons hmem with heq | hmem
        · injection heq with h1 _
          injection h1 with h1a h1b
          intro hcon
          have hlt := ih3 tn pos nk hcon
          rw [h1a, h1b, ← hpos0eq] at hlt
          omega
        · exact ih4 token tn pos pre hmem nk
      · simp only [if_neg ht] at hmem
        exact ih4 t tn pos pre hmem nk
    · intro t
      by_cases ht : t = token
      · subst t
        simp only [if_true]
        rw [List.nodup_cons]
        refine ⟨?_, ih5 token⟩
        intro hmem
        have hlt := ih1 token (insertTree s.trees 1) (insertStart s.trees 1)
          (⟨npk, token, shieldBase s.feeRatio x⟩ : CommitmentPreimage) hmem
        rw [← hpos0eq] at hlt
        omega
      · simp only [if_neg ht]
        exact ih5 t
  | transact caller w pub bp hN hM hC hBound hAdapt newNotes hOutputs rest spent' records
      openings hRoot hRemove hNullify hRecords =>
    generalize bp.treeNumber = treeNumber at hRoot hRemove hNullify ⊢
    have hpos0eq := insertStart_eq s.trees newNotes.length
    have hlenge := fun tn' => insertLeaves_leavesAt_length_ge s.trees
      (newNotes.map hashCommitment) tn'
    have htarget := insertLeaves_target_length s.trees
      (newNotes.map hashCommitment)
    simp only [List.length_map] at htarget
    have hperm := removeAll_perm hRemove
    have hpoolNodup := ih5 w.token
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> dsimp only [PoolState.leavesAt']
    · intro t tn pos pre hmem
      by_cases ht : t = w.token
      · subst ht
        simp only at hmem
        rcases List.mem_append.mp hmem with hnew | hrest
        · have htn := withTreePositionsFrom_treeNumber _ _ _ _ hnew
          simp only at htn
          have hlt := withTreePositionsFrom_pos_lt _ _ _ _ hnew
          simp only at hlt
          rw [htn]
          omega
        · have hmemold : ((tn, pos), pre) ∈ s.live w.token :=
            hperm.mem_iff.mpr (List.mem_append_right _ hrest)
          have hlt := ih1 w.token tn pos pre hmemold
          have hle := hlenge tn
          omega
      · simp only [if_neg ht] at hmem
        have hlt := ih1 t tn pos pre hmem
        have hle := hlenge tn
        omega
    · intro t t' tn pos pre pre' hmem hmem'
      by_cases ht : t = w.token <;> by_cases ht' : t' = w.token
      · subst ht; subst ht'
        simp only at hmem hmem'
        rcases List.mem_append.mp hmem with hnew | hrest <;>
          rcases List.mem_append.mp hmem' with hnew' | hrest'
        · exact ⟨rfl, withTreePositionsFrom_unique _ _ _ _ _ hnew hnew' rfl⟩
        · exfalso
          have htn := withTreePositionsFrom_treeNumber _ _ _ _ hnew
          simp only at htn
          have hge := withTreePositionsFrom_pos_ge _ _ _ _ hnew
          simp only at hge
          have hmemold : ((tn, pos), pre') ∈ s.live w.token :=
            hperm.mem_iff.mpr (List.mem_append_right _ hrest')
          have hlt := ih1 w.token tn pos pre' hmemold
          rw [htn, ← hpos0eq] at hlt
          omega
        · exfalso
          have htn := withTreePositionsFrom_treeNumber _ _ _ _ hnew'
          simp only at htn
          have hge := withTreePositionsFrom_pos_ge _ _ _ _ hnew'
          simp only at hge
          have hmemold : ((tn, pos), pre) ∈ s.live w.token :=
            hperm.mem_iff.mpr (List.mem_append_right _ hrest)
          have hlt := ih1 w.token tn pos pre hmemold
          rw [htn, ← hpos0eq] at hlt
          omega
        · have hmemold : ((tn, pos), pre) ∈ s.live w.token :=
            hperm.mem_iff.mpr (List.mem_append_right _ hrest)
          have hmemold' : ((tn, pos), pre') ∈ s.live w.token :=
            hperm.mem_iff.mpr (List.mem_append_right _ hrest')
          exact ih2 w.token w.token tn pos pre pre' hmemold hmemold'
      · subst ht
        simp only at hmem
        simp only [if_neg ht'] at hmem'
        rcases List.mem_append.mp hmem with hnew | hrest
        · exfalso
          have htn := withTreePositionsFrom_treeNumber _ _ _ _ hnew
          simp only at htn
          have hge := withTreePositionsFrom_pos_ge _ _ _ _ hnew
          simp only at hge
          have hlt := ih1 t' tn pos pre' hmem'
          rw [htn, ← hpos0eq] at hlt
          omega
        · have hmemold : ((tn, pos), pre) ∈ s.live w.token :=
            hperm.mem_iff.mpr (List.mem_append_right _ hrest)
          exact ih2 w.token t' tn pos pre pre' hmemold hmem'
      · subst ht'
        simp only at hmem'
        simp only [if_neg ht] at hmem
        rcases List.mem_append.mp hmem' with hnew' | hrest'
        · exfalso
          have htn := withTreePositionsFrom_treeNumber _ _ _ _ hnew'
          simp only at htn
          have hge := withTreePositionsFrom_pos_ge _ _ _ _ hnew'
          simp only at hge
          have hlt := ih1 t tn pos pre hmem
          rw [htn, ← hpos0eq] at hlt
          omega
        · have hmemold' : ((tn, pos), pre') ∈ s.live w.token :=
            hperm.mem_iff.mpr (List.mem_append_right _ hrest')
          exact ih2 t w.token tn pos pre pre' hmem hmemold'
      · simp only [if_neg ht] at hmem
        simp only [if_neg ht'] at hmem'
        exact ih2 t t' tn pos pre pre' hmem hmem'
    · intro tn pos nk hmem
      by_cases htn2 : tn = treeNumber
      · subst tn
        simp only at hmem
        rcases markSpent_superset hNullify (nullifier nk pos) hmem with hold | hnewmark
        · have hlt := ih3 treeNumber pos nk hold
          have hle := hlenge treeNumber
          omega
        · obtain ⟨i, hi⟩ := List.mem_ofFn.mp hnewmark
          have heqn : nullifier nk pos = nullifier (Term.val w.nullifyingKey) (w.leavesIndices i) := by
            rw [← hi]; exact hC.nullifiers i
          have hposeq : pos = w.leavesIndices i := (nullifier_inj heqn).2
          have hwanted : ((treeNumber, w.leavesIndices i),
              (⟨npk (masterPublicKey w.publicKey w.nullifyingKey) (w.randomIn i), w.token,
                w.valueIn i⟩ : CommitmentPreimage)) ∈ transactSpentPositions treeNumber w := by
            unfold transactSpentPositions
            exact List.mem_ofFn.mpr ⟨i, rfl⟩
          have hmemold := hperm.mem_iff.mpr (List.mem_append_left _ hwanted)
          have hlt := ih1 w.token treeNumber (w.leavesIndices i) _ hmemold
          have hle := hlenge treeNumber
          rw [← hposeq] at hlt
          omega
      · simp only [if_neg htn2] at hmem
        have hlt := ih3 tn pos nk hmem
        have hle := hlenge tn
        omega
    · intro t tn pos pre hmem nk
      by_cases ht : t = w.token
      · subst ht
        simp only at hmem
        rcases List.mem_append.mp hmem with hnew | hrest
        · have htn := withTreePositionsFrom_treeNumber _ _ _ _ hnew
          simp only at htn
          have hge := withTreePositionsFrom_pos_ge _ _ _ _ hnew
          simp only at hge
          intro hcon
          by_cases htn2 : tn = treeNumber
          · simp only [if_pos htn2] at hcon
            rcases markSpent_superset hNullify (nullifier nk pos) hcon with hold | hnewmark
            · have hold' := hold
              rw [← htn2] at hold'
              have hlt := ih3 tn pos nk hold'
              rw [htn, ← hpos0eq] at hlt
              omega
            · obtain ⟨i, hi⟩ := List.mem_ofFn.mp hnewmark
              have heqn : nullifier nk pos = nullifier (Term.val w.nullifyingKey) (w.leavesIndices i) := by
                rw [← hi]; exact hC.nullifiers i
              have hposeq : pos = w.leavesIndices i := (nullifier_inj heqn).2
              have hwanted : ((treeNumber, w.leavesIndices i),
                  (⟨npk (masterPublicKey w.publicKey w.nullifyingKey) (w.randomIn i), w.token,
                    w.valueIn i⟩ : CommitmentPreimage)) ∈ transactSpentPositions treeNumber w := by
                unfold transactSpentPositions
                exact List.mem_ofFn.mpr ⟨i, rfl⟩
              have hmemold2 := hperm.mem_iff.mpr (List.mem_append_left _ hwanted)
              have hlt2 := ih1 w.token treeNumber (w.leavesIndices i) _ hmemold2
              have hge2 : (leavesAt s.trees treeNumber).length ≤ pos := by
                rw [← htn2, htn, ← hpos0eq]; exact hge
              omega
          · simp only [if_neg htn2] at hcon
            have hlt := ih3 tn pos nk hcon
            rw [htn, ← hpos0eq] at hlt
            omega
        · have hmemold : ((tn, pos), pre) ∈ s.live w.token :=
            hperm.mem_iff.mpr (List.mem_append_right _ hrest)
          intro hcon
          by_cases htn2 : tn = treeNumber
          · simp only [if_pos htn2] at hcon
            rcases markSpent_superset hNullify (nullifier nk pos) hcon with hold | hnewmark
            · have hold' := hold
              rw [← htn2] at hold'
              exact ih4 w.token tn pos pre hmemold nk hold'
            · obtain ⟨i, hi⟩ := List.mem_ofFn.mp hnewmark
              have heqn : nullifier nk pos = nullifier (Term.val w.nullifyingKey) (w.leavesIndices i) := by
                rw [← hi]; exact hC.nullifiers i
              have hposeq : pos = w.leavesIndices i := (nullifier_inj heqn).2
              have hwanted : ((treeNumber, w.leavesIndices i),
                  (⟨npk (masterPublicKey w.publicKey w.nullifyingKey) (w.randomIn i), w.token,
                    w.valueIn i⟩ : CommitmentPreimage)) ∈ transactSpentPositions treeNumber w := by
                unfold transactSpentPositions
                exact List.mem_ofFn.mpr ⟨i, rfl⟩
              have hkeyeq : (treeNumber, w.leavesIndices i) = (tn, pos) := by
                rw [← htn2, hposeq]
              rw [hkeyeq] at hwanted
              have hvaleq := (ih2 w.token w.token tn pos pre
                (⟨npk (masterPublicKey w.publicKey w.nullifyingKey) (w.randomIn i), w.token,
                  w.valueIn i⟩ : CommitmentPreimage) hmemold
                (hperm.mem_iff.mpr (List.mem_append_left _ hwanted))).2
              rw [← hvaleq] at hwanted
              exact (removeAll_disjoint hpoolNodup hRemove) _ hwanted hrest
          · simp only [if_neg htn2] at hcon
            exact ih4 w.token tn pos pre hmemold nk hcon
      · simp only [if_neg ht] at hmem
        by_cases htn2 : tn = treeNumber
        · subst tn
          simp only at *
          intro hcon
          rcases markSpent_superset hNullify (nullifier nk pos) hcon with hold | hnewmark
          · exact ih4 t treeNumber pos pre hmem nk hold
          · obtain ⟨i, hi⟩ := List.mem_ofFn.mp hnewmark
            have heqn : nullifier nk pos = nullifier (Term.val w.nullifyingKey) (w.leavesIndices i) := by
              rw [← hi]; exact hC.nullifiers i
            have hposeq : pos = w.leavesIndices i := (nullifier_inj heqn).2
            have hwanted : ((treeNumber, w.leavesIndices i),
                (⟨npk (masterPublicKey w.publicKey w.nullifyingKey) (w.randomIn i), w.token,
                  w.valueIn i⟩ : CommitmentPreimage)) ∈ transactSpentPositions treeNumber w := by
              unfold transactSpentPositions
              exact List.mem_ofFn.mpr ⟨i, rfl⟩
            have hmemold2 := hperm.mem_iff.mpr (List.mem_append_left _ hwanted)
            have ht2 := (ih2 t w.token treeNumber pos pre
              (⟨npk (masterPublicKey w.publicKey w.nullifyingKey) (w.randomIn i), w.token,
                w.valueIn i⟩ : CommitmentPreimage) hmem
              (by rw [hposeq]; exact hmemold2)).1
            exact ht ht2
        · simp only [if_neg htn2] at *
          exact ih4 t tn pos pre hmem nk
    · intro t
      by_cases ht : t = w.token
      · subst ht
        simp only [if_true]
        rw [List.nodup_append]
        refine ⟨withTreePositionsFrom_nodup _ _ _, removeAll_nodup hpoolNodup hRemove, ?_⟩
        intro a ha b hb heq
        subst heq
        have htn := withTreePositionsFrom_treeNumber _ _ _ _ ha
        have hge := withTreePositionsFrom_pos_ge _ _ _ _ ha
        have hmemold : a ∈ s.live w.token := hperm.mem_iff.mpr (List.mem_append_right _ hb)
        have hlt := ih1 w.token a.1.1 a.1.2 a.2 hmemold
        rw [htn, ← hpos0eq] at hlt
        omega
      · simp only [if_neg ht]
        exact ih5 t
  | transactOwned w pub bp hN hM hC caller hCaller hBound hAdapt hNoUnshield rest spent'
      openings hRoot hRemove hNullify =>
    generalize bp.treeNumber = treeNumber at hRoot hRemove hNullify ⊢
    have hpos0eq := insertStart_eq s.trees (ownedNewNotes w).length
    have hlenge := fun tn' => insertLeaves_leavesAt_length_ge s.trees
      ((ownedNewNotes w).map hashCommitment) tn'
    have htarget := insertLeaves_target_length s.trees
      ((ownedNewNotes w).map hashCommitment)
    simp only [List.length_map] at htarget
    have hperm := removeAll_perm hRemove
    have hpoolNodup := ih5 w.token
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> dsimp only [PoolState.leavesAt']
    · intro t tn pos pre hmem
      by_cases ht : t = w.token
      · subst ht
        simp only at hmem
        rcases List.mem_append.mp hmem with hnew | hrest
        · have htn := withTreePositionsFrom_treeNumber _ _ _ _ hnew
          simp only at htn
          have hlt := withTreePositionsFrom_pos_lt _ _ _ _ hnew
          simp only at hlt
          rw [htn]
          omega
        · have hmemold : ((tn, pos), pre) ∈ s.live w.token :=
            hperm.mem_iff.mpr (List.mem_append_right _ hrest)
          have hlt := ih1 w.token tn pos pre hmemold
          have hle := hlenge tn
          omega
      · simp only [if_neg ht] at hmem
        have hlt := ih1 t tn pos pre hmem
        have hle := hlenge tn
        omega
    · intro t t' tn pos pre pre' hmem hmem'
      by_cases ht : t = w.token <;> by_cases ht' : t' = w.token
      · subst ht; subst ht'
        simp only at hmem hmem'
        rcases List.mem_append.mp hmem with hnew | hrest <;>
          rcases List.mem_append.mp hmem' with hnew' | hrest'
        · exact ⟨rfl, withTreePositionsFrom_unique _ _ _ _ _ hnew hnew' rfl⟩
        · exfalso
          have htn := withTreePositionsFrom_treeNumber _ _ _ _ hnew
          simp only at htn
          have hge := withTreePositionsFrom_pos_ge _ _ _ _ hnew
          simp only at hge
          have hmemold : ((tn, pos), pre') ∈ s.live w.token :=
            hperm.mem_iff.mpr (List.mem_append_right _ hrest')
          have hlt := ih1 w.token tn pos pre' hmemold
          rw [htn, ← hpos0eq] at hlt
          omega
        · exfalso
          have htn := withTreePositionsFrom_treeNumber _ _ _ _ hnew'
          simp only at htn
          have hge := withTreePositionsFrom_pos_ge _ _ _ _ hnew'
          simp only at hge
          have hmemold : ((tn, pos), pre) ∈ s.live w.token :=
            hperm.mem_iff.mpr (List.mem_append_right _ hrest)
          have hlt := ih1 w.token tn pos pre hmemold
          rw [htn, ← hpos0eq] at hlt
          omega
        · have hmemold : ((tn, pos), pre) ∈ s.live w.token :=
            hperm.mem_iff.mpr (List.mem_append_right _ hrest)
          have hmemold' : ((tn, pos), pre') ∈ s.live w.token :=
            hperm.mem_iff.mpr (List.mem_append_right _ hrest')
          exact ih2 w.token w.token tn pos pre pre' hmemold hmemold'
      · subst ht
        simp only at hmem
        simp only [if_neg ht'] at hmem'
        rcases List.mem_append.mp hmem with hnew | hrest
        · exfalso
          have htn := withTreePositionsFrom_treeNumber _ _ _ _ hnew
          simp only at htn
          have hge := withTreePositionsFrom_pos_ge _ _ _ _ hnew
          simp only at hge
          have hlt := ih1 t' tn pos pre' hmem'
          rw [htn, ← hpos0eq] at hlt
          omega
        · have hmemold : ((tn, pos), pre) ∈ s.live w.token :=
            hperm.mem_iff.mpr (List.mem_append_right _ hrest)
          exact ih2 w.token t' tn pos pre pre' hmemold hmem'
      · subst ht'
        simp only at hmem'
        simp only [if_neg ht] at hmem
        rcases List.mem_append.mp hmem' with hnew' | hrest'
        · exfalso
          have htn := withTreePositionsFrom_treeNumber _ _ _ _ hnew'
          simp only at htn
          have hge := withTreePositionsFrom_pos_ge _ _ _ _ hnew'
          simp only at hge
          have hlt := ih1 t tn pos pre hmem
          rw [htn, ← hpos0eq] at hlt
          omega
        · have hmemold' : ((tn, pos), pre') ∈ s.live w.token :=
            hperm.mem_iff.mpr (List.mem_append_right _ hrest')
          exact ih2 t w.token tn pos pre pre' hmem hmemold'
      · simp only [if_neg ht] at hmem
        simp only [if_neg ht'] at hmem'
        exact ih2 t t' tn pos pre pre' hmem hmem'
    · intro tn pos nk hmem
      by_cases htn2 : tn = treeNumber
      · subst tn
        simp only at hmem
        rcases markSpent_superset hNullify (nullifier nk pos) hmem with hold | hnewmark
        · have hlt := ih3 treeNumber pos nk hold
          have hle := hlenge treeNumber
          omega
        · obtain ⟨i, hi⟩ := List.mem_ofFn.mp hnewmark
          have heqn : nullifier nk pos = nullifier pub.ownerField (w.leavesIndices i) := by
            rw [← hi]; exact hC.nullifiers i
          have hposeq : pos = w.leavesIndices i := (nullifier_inj heqn).2
          have hwanted : ((treeNumber, w.leavesIndices i),
              (⟨npk pub.ownerField (w.randomIn i), w.token, w.valueIn i⟩ : CommitmentPreimage)) ∈
              ownedSpentPositions treeNumber pub w := by
            unfold ownedSpentPositions
            exact List.mem_ofFn.mpr ⟨i, rfl⟩
          have hmemold := hperm.mem_iff.mpr (List.mem_append_left _ hwanted)
          have hlt := ih1 w.token treeNumber (w.leavesIndices i) _ hmemold
          have hle := hlenge treeNumber
          rw [← hposeq] at hlt
          omega
      · simp only [if_neg htn2] at hmem
        have hlt := ih3 tn pos nk hmem
        have hle := hlenge tn
        omega
    · intro t tn pos pre hmem nk
      by_cases ht : t = w.token
      · subst ht
        simp only at hmem
        rcases List.mem_append.mp hmem with hnew | hrest
        · have htn := withTreePositionsFrom_treeNumber _ _ _ _ hnew
          simp only at htn
          have hge := withTreePositionsFrom_pos_ge _ _ _ _ hnew
          simp only at hge
          intro hcon
          by_cases htn2 : tn = treeNumber
          · simp only [if_pos htn2] at hcon
            rcases markSpent_superset hNullify (nullifier nk pos) hcon with hold | hnewmark
            · have hold' := hold
              rw [← htn2] at hold'
              have hlt := ih3 tn pos nk hold'
              rw [htn, ← hpos0eq] at hlt
              omega
            · obtain ⟨i, hi⟩ := List.mem_ofFn.mp hnewmark
              have heqn : nullifier nk pos = nullifier pub.ownerField (w.leavesIndices i) := by
                rw [← hi]; exact hC.nullifiers i
              have hposeq : pos = w.leavesIndices i := (nullifier_inj heqn).2
              have hwanted : ((treeNumber, w.leavesIndices i),
                  (⟨npk pub.ownerField (w.randomIn i), w.token, w.valueIn i⟩ : CommitmentPreimage)) ∈
                  ownedSpentPositions treeNumber pub w := by
                unfold ownedSpentPositions
                exact List.mem_ofFn.mpr ⟨i, rfl⟩
              have hmemold2 := hperm.mem_iff.mpr (List.mem_append_left _ hwanted)
              have hlt2 := ih1 w.token treeNumber (w.leavesIndices i) _ hmemold2
              have hge2 : (leavesAt s.trees treeNumber).length ≤ pos := by
                rw [← htn2, htn, ← hpos0eq]; exact hge
              omega
          · simp only [if_neg htn2] at hcon
            have hlt := ih3 tn pos nk hcon
            rw [htn, ← hpos0eq] at hlt
            omega
        · have hmemold : ((tn, pos), pre) ∈ s.live w.token :=
            hperm.mem_iff.mpr (List.mem_append_right _ hrest)
          intro hcon
          by_cases htn2 : tn = treeNumber
          · simp only [if_pos htn2] at hcon
            rcases markSpent_superset hNullify (nullifier nk pos) hcon with hold | hnewmark
            · have hold' := hold
              rw [← htn2] at hold'
              exact ih4 w.token tn pos pre hmemold nk hold'
            · obtain ⟨i, hi⟩ := List.mem_ofFn.mp hnewmark
              have heqn : nullifier nk pos = nullifier pub.ownerField (w.leavesIndices i) := by
                rw [← hi]; exact hC.nullifiers i
              have hposeq : pos = w.leavesIndices i := (nullifier_inj heqn).2
              have hwanted : ((treeNumber, w.leavesIndices i),
                  (⟨npk pub.ownerField (w.randomIn i), w.token, w.valueIn i⟩ : CommitmentPreimage)) ∈
                  ownedSpentPositions treeNumber pub w := by
                unfold ownedSpentPositions
                exact List.mem_ofFn.mpr ⟨i, rfl⟩
              have hkeyeq : (treeNumber, w.leavesIndices i) = (tn, pos) := by
                rw [← htn2, hposeq]
              rw [hkeyeq] at hwanted
              have hvaleq := (ih2 w.token w.token tn pos pre
                (⟨npk pub.ownerField (w.randomIn i), w.token, w.valueIn i⟩ : CommitmentPreimage) hmemold
                (hperm.mem_iff.mpr (List.mem_append_left _ hwanted))).2
              rw [← hvaleq] at hwanted
              exact (removeAll_disjoint hpoolNodup hRemove) _ hwanted hrest
          · simp only [if_neg htn2] at hcon
            exact ih4 w.token tn pos pre hmemold nk hcon
      · simp only [if_neg ht] at hmem
        by_cases htn2 : tn = treeNumber
        · subst tn
          simp only at *
          intro hcon
          rcases markSpent_superset hNullify (nullifier nk pos) hcon with hold | hnewmark
          · exact ih4 t treeNumber pos pre hmem nk hold
          · obtain ⟨i, hi⟩ := List.mem_ofFn.mp hnewmark
            have heqn : nullifier nk pos = nullifier pub.ownerField (w.leavesIndices i) := by
              rw [← hi]; exact hC.nullifiers i
            have hposeq : pos = w.leavesIndices i := (nullifier_inj heqn).2
            have hwanted : ((treeNumber, w.leavesIndices i),
                (⟨npk pub.ownerField (w.randomIn i), w.token, w.valueIn i⟩ : CommitmentPreimage)) ∈
                ownedSpentPositions treeNumber pub w := by
              unfold ownedSpentPositions
              exact List.mem_ofFn.mpr ⟨i, rfl⟩
            have hmemold2 := hperm.mem_iff.mpr (List.mem_append_left _ hwanted)
            have ht2 := (ih2 t w.token treeNumber pos pre
              (⟨npk pub.ownerField (w.randomIn i), w.token, w.valueIn i⟩ : CommitmentPreimage) hmem
              (by rw [hposeq]; exact hmemold2)).1
            exact ht ht2
        · simp only [if_neg htn2] at *
          exact ih4 t tn pos pre hmem nk
    · intro t
      by_cases ht : t = w.token
      · subst ht
        simp only [if_true]
        rw [List.nodup_append]
        refine ⟨withTreePositionsFrom_nodup _ _ _, removeAll_nodup hpoolNodup hRemove, ?_⟩
        intro a ha b hb heq
        subst heq
        have htn := withTreePositionsFrom_treeNumber _ _ _ _ ha
        have hge := withTreePositionsFrom_pos_ge _ _ _ _ ha
        have hmemold : a ∈ s.live w.token := hperm.mem_iff.mpr (List.mem_append_right _ hb)
        have hlt := ih1 w.token a.1.1 a.1.2 a.2 hmemold
        rw [htn, ← hpos0eq] at hlt
        omega
      · simp only [if_neg ht]
        exact ih5 t

theorem reachable_live_spent_invariant {s : PoolState} (h : Reachable s) :
    LiveSpentInvariant s := by
  induction h with
  | genesis r a b => exact genesis_live_spent_invariant r a b
  | step _ hstep ih => exact step_preserves_live_spent_invariant ih hstep

/--
**A live note's nullifier is not in `spent`.** For any reachable state, any live entry
`((tn, pos), pre) ∈ s.live t` and any nullifying key `nk`, `nullifier nk pos` is not
among tree `tn`'s spent nullifiers. Kept as a lemma because pool-level theorems need
it: `owned_merge_can_happen` and `spend_not_blocked` both need the nullifier of a live
note to be fresh (finding P-5: it no longer exists for an adjudicator storage slot).
Proved from the ghost invariant `LiveSpentInvariant`: a position still live was never
named by any earlier `transact`/`transactOwned`, because a spend that named it would
have removed it from `live` at that same step (`removeAll_disjoint`, keyed by the
invariant's no-duplicate-entry fact). -/
theorem live_note_unspent (s : ReachableState Pool.machine) (t : Token) (tn pos : Nat)
    (pre : CommitmentPreimage) (hmem : ((tn, pos), pre) ∈ s.state.live t) (nk : Term) :
    nullifier nk pos ∉ s.state.spent tn := obtain_reach% ⟨s, h : Reachable s⟩ := s;
  (reachable_live_spent_invariant h).2.2.2.1 t tn pos pre hmem nk

/-! ### A live entry's position names the leaf that holds its commitment -/

/-- One step preserves "every live entry's position holds its own commitment as a
    leaf": a surviving entry's leaf is unchanged (`insertLeaves_leavesAt_stable`,
    using `ihrange` for the in-range precondition), and a freshly-inserted entry's
    leaf is exactly its own hash by construction
    (`insertLeaves_leavesAt_new_matches`/`withTreePositionsFrom_leaf_matches`). The
    lookup default `emptyLeaf` is never read, because every live position is in range
    (`LiveSpentInvariant`, first part). A
    standalone wrapper (states inferred from `hstep`) so
    `reachable_live_leaf_matches`'s induction never needs to name the previous state
    by hand. -/
theorem step_live_leaf_matches {s s' : PoolState} (hstep : Step s s')
    (ihmatch : ∀ t tn pos pre, ((tn, pos), pre) ∈ s.live t →
      (s.leavesAt' tn).getD pos emptyLeaf = hashCommitment pre)
    (ihrange : ∀ t tn pos pre, ((tn, pos), pre) ∈ s.live t → pos < (s.leavesAt' tn).length) :
    ∀ t tn pos pre, ((tn, pos), pre) ∈ s'.live t →
      (s'.leavesAt' tn).getD pos emptyLeaf = hashCommitment pre := by
  cases hstep with
  | setFeeRatio => exact ihmatch
  | shield token x npk hValue hSpendable =>
    intro t tn pos pre hmem
    by_cases ht : t = token
    · subst t
      simp only at hmem
      rcases List.eq_or_mem_of_mem_cons hmem with heq | hmem
      · obtain ⟨base, hbaselen, hbase⟩ := insertLeaves_leavesAt_new_matches s.trees [hashCommitment (⟨npk, token, shieldBase s.feeRatio x⟩ : CommitmentPreimage)]
            (insertTree s.trees 1) rfl
        injection heq with h1 h2
        injection h1 with h1a h1b
        simp only [List.length_singleton] at hbaselen
        rw [h1a, h1b, h2]
        dsimp only [PoolState.leavesAt']
        rw [hbase, ← hbaselen]
        exact List.getD_concat_length base _ _
      · have hmatch := ihmatch token tn pos pre hmem
        have hr := ihrange token tn pos pre hmem
        dsimp only [PoolState.leavesAt']
        rw [insertLeaves_leavesAt_stable s.trees
          [hashCommitment (⟨npk, token, shieldBase s.feeRatio x⟩ : CommitmentPreimage)] tn pos
          emptyLeaf hr]
        exact hmatch
    · simp only [if_neg ht] at hmem
      have hmatch := ihmatch t tn pos pre hmem
      have hr := ihrange t tn pos pre hmem
      dsimp only [PoolState.leavesAt']
      rw [insertLeaves_leavesAt_stable s.trees
        [hashCommitment (⟨npk, token, shieldBase s.feeRatio x⟩ : CommitmentPreimage)] tn pos
        emptyLeaf hr]
      exact hmatch
  | transact caller w pub bp hN hM hC hBound hAdapt newNotes hOutputs rest spent' records
      openings hRoot hRemove hNullify hRecords =>
    intro t tn pos pre hmem
    have hlenEq : (newNotes.map hashCommitment).length = newNotes.length := by (simp? says simp only [List.length_map])
    by_cases ht : t = w.token
    · subst ht
      simp only at hmem
      rcases List.mem_append.mp hmem with hnew | hrest
      · have htn : insertTree s.trees newNotes.length =
            insertTree s.trees (newNotes.map hashCommitment).length := by
          rw [hlenEq]
        obtain ⟨base, hbaselen, hbase⟩ := insertLeaves_leavesAt_new_matches s.trees (newNotes.map hashCommitment)
            (insertTree s.trees (newNotes.map hashCommitment).length) rfl
        rw [← htn] at hbase
        rw [hlenEq] at hbaselen
        have htn' := withTreePositionsFrom_treeNumber _ _ _ _ hnew
        simp only at htn'
        have hleaf := withTreePositionsFrom_leaf_matches hashCommitment base
          (insertTree s.trees newNotes.length)
          (insertStart s.trees newNotes.length) newNotes hbaselen emptyLeaf ((tn, pos), pre) hnew
        dsimp only [PoolState.leavesAt']
        rw [htn', hbase]
        exact hleaf
      · have hmemold : ((tn, pos), pre) ∈ s.live w.token :=
          (removeAll_perm hRemove).mem_iff.mpr (List.mem_append_right _ hrest)
        have hmatch := ihmatch w.token tn pos pre hmemold
        have hr := ihrange w.token tn pos pre hmemold
        dsimp only [PoolState.leavesAt']
        rw [insertLeaves_leavesAt_stable s.trees
          (newNotes.map hashCommitment) tn pos emptyLeaf hr]
        exact hmatch
    · simp only [if_neg ht] at hmem
      have hmatch := ihmatch t tn pos pre hmem
      have hr := ihrange t tn pos pre hmem
      dsimp only [PoolState.leavesAt']
      rw [insertLeaves_leavesAt_stable s.trees
        (newNotes.map hashCommitment) tn pos emptyLeaf hr]
      exact hmatch
  | transactOwned w pub bp hN hM hC caller hCaller hBound hAdapt hNoUnshield rest spent'
      openings hRoot hRemove hNullify =>
    intro t tn pos pre hmem
    have hlenEq : ((ownedNewNotes w).map hashCommitment).length = (ownedNewNotes w).length := by (simp? says simp only [List.length_map])
    by_cases ht : t = w.token
    · subst ht
      simp only at hmem
      rcases List.mem_append.mp hmem with hnew | hrest
      · have htn : insertTree s.trees (ownedNewNotes w).length =
            insertTree s.trees ((ownedNewNotes w).map hashCommitment).length := by
          rw [hlenEq]
        obtain ⟨base, hbaselen, hbase⟩ := insertLeaves_leavesAt_new_matches s.trees ((ownedNewNotes w).map hashCommitment)
            (insertTree s.trees ((ownedNewNotes w).map hashCommitment).length) rfl
        rw [← htn] at hbase
        rw [hlenEq] at hbaselen
        have htn' := withTreePositionsFrom_treeNumber _ _ _ _ hnew
        simp only at htn'
        have hleaf := withTreePositionsFrom_leaf_matches hashCommitment base
          (insertTree s.trees (ownedNewNotes w).length)
          (insertStart s.trees (ownedNewNotes w).length) (ownedNewNotes w) hbaselen emptyLeaf
          ((tn, pos), pre) hnew
        dsimp only [PoolState.leavesAt']
        rw [htn', hbase]
        exact hleaf
      · have hmemold : ((tn, pos), pre) ∈ s.live w.token :=
          (removeAll_perm hRemove).mem_iff.mpr (List.mem_append_right _ hrest)
        have hmatch := ihmatch w.token tn pos pre hmemold
        have hr := ihrange w.token tn pos pre hmemold
        dsimp only [PoolState.leavesAt']
        rw [insertLeaves_leavesAt_stable s.trees
          ((ownedNewNotes w).map hashCommitment) tn pos emptyLeaf hr]
        exact hmatch
    · simp only [if_neg ht] at hmem
      have hmatch := ihmatch t tn pos pre hmem
      have hr := ihrange t tn pos pre hmem
      dsimp only [PoolState.leavesAt']
      rw [insertLeaves_leavesAt_stable s.trees
        ((ownedNewNotes w).map hashCommitment) tn pos emptyLeaf hr]
      exact hmatch

/-- Every live entry at every reachable state still holds, at its own recorded
    position, a leaf that hashes to its own recorded preimage. -/
theorem reachable_live_leaf_matches {s : PoolState} (h : Reachable s) :
    ∀ t tn pos pre, ((tn, pos), pre) ∈ s.live t →
      (s.leavesAt' tn).getD pos emptyLeaf = hashCommitment pre := by
  induction h with
  | genesis _ _ _ => intro t tn pos pre hmem; (simp? [genesis] at hmem says simp only [genesis, List.not_mem_nil] at hmem)
  | step hs hstep ih =>
    exact step_live_leaf_matches hstep ih (reachable_live_spent_invariant hs).1

/--
**A live entry's position holds the leaf of its commitment.** For any reachable state
and any live entry `((tn, pos), pre) ∈ s.live t`, position `pos` of tree `tn` holds
exactly `hashCommitment pre`. Kept as a lemma because a pool-level theorem needs it:
`owned_merge_can_happen` builds each input's Merkle path from this leaf (finding P-5).
The lookup is an `Option`; the statement implies the position exists (finding P-8).
Proved from `reachable_live_leaf_matches` and the range part of
`LiveSpentInvariant`. -/
theorem live_leaf_matches (s : ReachableState Pool.machine) (t : Token) (tn pos : Nat)
    (pre : CommitmentPreimage) (hmem : ((tn, pos), pre) ∈ s.state.live t) :
    (s.state.leavesAt' tn)[pos]? = some (hashCommitment pre) := by
  obtain_reach ⟨s, h : Reachable s⟩ := s
  have hmatch := reachable_live_leaf_matches h t tn pos pre hmem
  have hrange := (reachable_live_spent_invariant h).1 t tn pos pre hmem
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hrange] at hmatch
  rw [List.getElem?_eq_getElem hrange]
  exact congrArg some hmatch

/-! ### A leaf is live or its note is spent -/

/-- `nk` is the nullifier key of the note `pre`: `Term.val` of the nullifying key when
    the note key is a user key (`npk (masterPublicKey pk k) r`), and the owner field
    when the note key is an owned key (`npk (Term.val o) r`). A plain spend marks
    `nullifier (Term.val k) pos`; an owned spend marks `nullifier (Term.val o) pos`. -/
def NoteKey (pre : CommitmentPreimage) (nk : Term) : Prop :=
  (∃ (pk : Nat × Nat) (k r : Nat), pre.npk = npk (masterPublicKey pk k) r ∧ nk = Term.val k) ∨
  (∃ (o r : Nat), pre.npk = npk (Term.val o) r ∧ nk = Term.val o)

/-- Every leaf that holds a commitment is live at its position, or its note's own
    nullifier is spent in its tree. The converse of `live_note_unspent`: a contract that
    checks the root and the nullifier can conclude that the note is live. -/
structure LeafLiveOrSpent (s : PoolState) : Prop where
  leaf : ∀ tn pos pre, (s.leavesAt' tn)[pos]? = some (hashCommitment pre) →
    ((tn, pos), pre) ∈ s.live pre.token ∨ ∃ nk, NoteKey pre nk ∧ nullifier nk pos ∈ s.spent tn

theorem genesis_leafLiveOrSpent (r : FeeRatio) (feeAdmin treasury : Term) :
    LeafLiveOrSpent (genesis r feeAdmin treasury) := by
  refine ⟨fun tn pos pre h => ?_⟩
  cases tn with
  | zero =>
    simp only [genesis, PoolState.leavesAt', leavesAt, genesisTrees, List.getElem?_cons_zero,
      List.getElem?_nil, reduceCtorEq] at h
  | succ n =>
    simp only [genesis, PoolState.leavesAt', leavesAt, genesisTrees, List.getElem?_cons_succ,
      List.getElem?_nil, reduceCtorEq] at h

/-- The shape of a spend-like step from `s` to `s'`: the step removes `wanted` from the
    live entries of `tok`, marks `nulls` in tree `treeNumber`, and appends `notes` of
    token `tok` as new leaves and as new live entries. Every removed entry is in the
    tree the step marks, and the step marks its note's nullifier (`wanted_spent`). A
    shield is the case with nothing removed and nothing marked. -/
structure SpendShape (s s' : PoolState) (tok : Token) (notes : List CommitmentPreimage)
    (treeNumber : Nat) (wanted rest : List ((Nat × Nat) × CommitmentPreimage))
    (nulls : List Term) (spent' : NullifierSet) : Prop where
  remove : removeAll (s.live tok) wanted = some rest
  nullify : markSpent (s.spent treeNumber) nulls = some spent'
  wanted_spent : ∀ e ∈ wanted,
    e.1.1 = treeNumber ∧ ∃ nk, NoteKey e.2 nk ∧ nullifier nk e.1.2 ∈ nulls
  notes_token : ∀ n ∈ notes, n.token = tok
  live : ∀ t, s'.live t = if t = tok
    then withTreePositionsFrom (insertTree s.trees notes.length)
      (insertStart s.trees notes.length) notes ++ rest
    else s.live t
  spent : ∀ n, s'.spent n = if n = treeNumber then spent' else s.spent n
  trees : s'.trees = insertLeaves s.trees (notes.map hashCommitment)

/-- One spend-shaped step preserves `LeafLiveOrSpent`. An old leaf keeps its live
    entry unless the step spent it, and then the step marked its nullifier
    (`SpendShape.wanted_spent`). A new leaf gets its live entry at its own position
    (`withTreePositionsFrom_mem_of_getElem?`). -/
theorem spendShape_preserves_leafLiveOrSpent {s s' : PoolState} (ih : LeafLiveOrSpent s)
    (tok : Token) (notes : List CommitmentPreimage) (treeNumber : Nat)
    (wanted rest : List ((Nat × Nat) × CommitmentPreimage)) (nulls : List Term)
    (spent' : NullifierSet) (h : SpendShape s s' tok notes treeNumber wanted rest nulls spent') :
    LeafLiveOrSpent s' := by
  obtain ⟨hRemove, hNullify, hWanted, hNotes, hlive, hspent, htrees⟩ := h
  refine ⟨fun tn pos pre hleaf => ?_⟩
  have hspentMono : ∀ n x, x ∈ s.spent n → x ∈ s'.spent n := by
    intro n x hx
    rw [hspent]
    by_cases hn : n = treeNumber
    · rw [if_pos hn]; subst hn; exact markSpent_subset hNullify x hx
    · rw [if_neg hn]; exact hx
  have hlenEq : (notes.map hashCommitment).length = notes.length := by rw [List.length_map]
  -- An old leaf: its entry is live or spent at `s`.
  have hold : (s.leavesAt' tn)[pos]? = some (hashCommitment pre) →
      ((tn, pos), pre) ∈ s'.live pre.token ∨
        ∃ nk, NoteKey pre nk ∧ nullifier nk pos ∈ s'.spent tn := by
    intro hleafOld
    rcases ih.leaf tn pos pre hleafOld with hlv | ⟨nk, hkey, hsp⟩
    · by_cases ht : pre.token = tok
      · rw [ht] at hlv
        rcases (removeAll_perm hRemove).mem_iff.mp hlv |> List.mem_append.mp with hw | hr
        · obtain ⟨htn, nk, hkey, hnull⟩ := hWanted _ hw
          simp only at htn
          refine Or.inr ⟨nk, hkey, ?_⟩
          rw [hspent, htn, if_pos rfl]
          exact markSpent_mem hNullify _ hnull
        · refine Or.inl ?_
          rw [hlive, if_pos ht]
          exact List.mem_append_right _ hr
      · refine Or.inl ?_
        rw [hlive, if_neg ht]
        exact hlv
    · exact Or.inr ⟨nk, hkey, hspentMono tn _ hsp⟩
  dsimp only [PoolState.leavesAt'] at hleaf
  rw [htrees, insertLeaves_leavesAt] at hleaf
  by_cases htn : tn = insertTree s.trees (notes.map hashCommitment).length
  · rw [if_pos htn] at hleaf
    rw [List.getElem?_append] at hleaf
    by_cases hpos : pos < (leavesAt s.trees tn).length
    · rw [if_pos hpos] at hleaf
      exact hold hleaf
    · rw [if_neg hpos] at hleaf
      rw [List.getElem?_map] at hleaf
      cases hj : notes[pos - (leavesAt s.trees tn).length]? with
      | none =>
        rw [hj] at hleaf
        exact absurd hleaf (by (simp? says simp only [Option.map_none, reduceCtorEq, not_false_eq_true]))
      | some pre' =>
        rw [hj] at hleaf
        simp only [Option.map_some, Option.some.injEq] at hleaf
        have hpre : pre' = pre := hashCommitment_inj hleaf
        subst hpre
        refine Or.inl ?_
        rw [hlive, if_pos (hNotes pre' (List.mem_of_getElem? hj))]
        refine List.mem_append_left _ ?_
        have hstart : insertStart s.trees notes.length = (leavesAt s.trees tn).length := by
          rw [insertStart_eq, ← hlenEq, ← htn]
        rw [hlenEq] at htn
        have hpos' : pos =
            insertStart s.trees notes.length + (pos - (leavesAt s.trees tn).length) := by
          rw [hstart]; omega
        rw [hpos']
        subst htn
        exact withTreePositionsFrom_mem_of_getElem? _ _ notes _ hj
  · rw [if_neg htn] at hleaf
    exact hold hleaf

theorem step_preserves_leafLiveOrSpent {s s' : PoolState} (ih : LeafLiveOrSpent s)
    (hstep : Step s s') : LeafLiveOrSpent s' := by
  cases hstep with
  | setFeeRatio => exact ⟨ih.leaf⟩
  | shield token x npk hValue hSpendable =>
    refine spendShape_preserves_leafLiveOrSpent ih token [⟨npk, token, shieldBase s.feeRatio x⟩]
      0 [] (s.live token) [] (s.spent 0) ⟨rfl, rfl, fun e he => absurd he List.not_mem_nil,
      fun n hn => by rw [List.mem_singleton] at hn; subst hn; rfl, ?_, ?_, rfl⟩
    · intro t
      dsimp only
      by_cases ht : t = token
      · subst ht
        rw [if_pos rfl, if_pos rfl]
        rfl
      · rw [if_neg ht, if_neg ht]
    · intro n
      dsimp only
      by_cases hn : n = 0
      · rw [if_pos hn, hn]
      · rw [if_neg hn]
  | transact caller w pub bp hN hM hC hBound hAdapt newNotes hOutputs rest spent' records
      openings hRoot hRemove hNullify hRecords =>
    refine spendShape_preserves_leafLiveOrSpent ih w.token newNotes bp.treeNumber
      (transactSpentPositions bp.treeNumber w) rest (List.ofFn pub.nullifiers) spent'
      ⟨hRemove, hNullify, ?_, ?_, fun t => rfl, fun n => rfl, rfl⟩
    · intro e he
      obtain ⟨i, hi⟩ := List.mem_ofFn.mp he
      subst hi
      refine ⟨rfl, Term.val w.nullifyingKey,
        Or.inl ⟨w.publicKey, w.nullifyingKey, w.randomIn i, rfl, rfl⟩, ?_⟩
      rw [← hC.nullifiers i]
      exact List.mem_ofFn.mpr ⟨i, rfl⟩
    · intro n hn
      obtain ⟨j, hj⟩ := List.mem_ofFn.mp (unshieldRefines_mem hOutputs n hn)
      rw [← hj]
  | transactOwned w pub bp hN hM hC caller hCaller hBound hAdapt hNoUnshield rest spent'
      openings hRoot hRemove hNullify =>
    refine spendShape_preserves_leafLiveOrSpent ih w.token (ownedNewNotes w) bp.treeNumber
      (ownedSpentPositions bp.treeNumber pub w) rest (List.ofFn pub.nullifiers) spent'
      ⟨hRemove, hNullify, ?_, ?_, fun t => rfl, fun n => rfl, rfl⟩
    · intro e he
      obtain ⟨i, hi⟩ := List.mem_ofFn.mp he
      subst hi
      refine ⟨rfl, pub.ownerField, Or.inr ⟨pub.owner, w.randomIn i, rfl, rfl⟩, ?_⟩
      rw [← hC.nullifiers i]
      exact List.mem_ofFn.mpr ⟨i, rfl⟩
    · intro n hn
      obtain ⟨j, hj⟩ := List.mem_ofFn.mp hn
      rw [← hj]

/-- Every leaf of every reachable state is live or spent. -/
theorem leaf_live_or_spent (s : ReachableState Pool.machine) : LeafLiveOrSpent s.state := by
  obtain_reach ⟨s, h : Reachable s⟩ := s
  induction h with
  | genesis r a b => exact genesis_leafLiveOrSpent r a b
  | step _ hstep ih => exact step_preserves_leafLiveOrSpent ih hstep

/-! ### Every live note is spendable -/

/-- Every live note's value passes the circuit's input range check (`Spendable`,
    `ArmadaLean.RangeCheck`). -/
def LiveValuesSpendable (s : PoolState) : Prop :=
  ∀ t p, p ∈ s.live t → Spendable p.2.value

theorem genesis_live_values_spendable (r : FeeRatio) (feeAdmin treasury : Term) :
    LiveValuesSpendable (genesis r feeAdmin treasury) := by
  intro t p hp
  (simp? [genesis] at hp says simp only [genesis, List.not_mem_nil] at hp)

theorem step_preserves_live_values_spendable {s s' : PoolState} (ih : LiveValuesSpendable s)
    (hstep : Step s s') : LiveValuesSpendable s' := by
  cases hstep with
  | setFeeRatio => exact ih
  | shield token x npk hValue hSpendable =>
    intro t p hp
    by_cases ht : t = token
    · subst t
      simp only at hp
      rcases List.eq_or_mem_of_mem_cons hp with heq | hp
      · rw [heq]
        exact hSpendable
      · exact ih token p hp
    · simp only [if_neg ht] at hp
      exact ih t p hp
  | transact caller w pub bp hN hM hC hBound hAdapt newNotes hOutputs rest spent' records
      openings hRoot hRemove hNullify hRecords =>
    intro t p hp
    by_cases ht : t = w.token
    · subst ht
      simp only at hp
      rcases List.mem_append.mp hp with hnew | hrest
      · have hqnew : p.2 ∈ newNotes := withTreePositionsFrom_snd_mem _ _ _ _ hnew
        have hmemall := unshieldRefines_mem hOutputs p.2 hqnew
        unfold transactAllOutputs at hmemall
        obtain ⟨j, hj⟩ := List.mem_ofFn.mp hmemall
        rw [← hj]
        exact hC.rangeOut j
      · have hmemold : p ∈ s.live w.token :=
          (removeAll_perm hRemove).mem_iff.mpr (List.mem_append_right _ hrest)
        exact ih w.token p hmemold
    · simp only [if_neg ht] at hp
      exact ih t p hp
  | transactOwned w pub bp hN hM hC caller hCaller hBound hAdapt hNoUnshield rest spent'
      openings hRoot hRemove hNullify =>
    intro t p hp
    by_cases ht : t = w.token
    · subst ht
      simp only at hp
      rcases List.mem_append.mp hp with hnew | hrest
      · have hqnew : p.2 ∈ ownedNewNotes w := withTreePositionsFrom_snd_mem _ _ _ _ hnew
        unfold ownedNewNotes at hqnew
        obtain ⟨j, hj⟩ := List.mem_ofFn.mp hqnew
        rw [← hj]
        exact hC.rangeOut j
      · have hmemold : p ∈ s.live w.token :=
          (removeAll_perm hRemove).mem_iff.mpr (List.mem_append_right _ hrest)
        exact ih w.token p hmemold
    · simp only [if_neg ht] at hp
      exact ih t p hp

/--
**Every note the pool records as live is spendable.** Its value passes the circuit's
input range check (`Spendable`): a transact or owned output passed the output check
(`Constrained.rangeOut`/`OwnedConstrained.rangeOut`, Transact.circom:125-129,
TransactOwned.circom:117-121), and a shield's note carries `Step.shield`'s
`hSpendable` (`CommitmentPreimage.value : uint120`, PoolTypes.sol:82). The pool needs
this for liveness, not for safety: a note whose value failed the check could never be
an input. The number 120 stays in the circuit layer (finding P-6). Kept because
`owned_merge_can_happen` needs it for its inputs (finding P-5). -/
theorem live_values_spendable (s : ReachableState Pool.machine) :
    LiveValuesSpendable s.state := by
  obtain_reach ⟨s, h : Reachable s⟩ := s
  induction h with
  | genesis r a b => exact genesis_live_values_spendable r a b
  | step _ hstep ih => exact step_preserves_live_values_spendable ih hstep

/-! ### No step blocks a pending spend (theorem 1 of the channel design)

The pool has no pause and no admin (module comment of `ArmadaLean.Pool`, finding P-3).
`Step.transact` and `Step.transactOwned` read the pool state in three checks only:
`hRoot`, `hRemove` and `hNullify`. `SpendEnabled` is those three checks. Every other
hypothesis of the two constructors reads only the transaction, so a step from `s'` with
the same transaction exists exactly when `SpendEnabled` holds at `s'`. -/

/-- The checks of a spend that read the pool state: the root is one of tree `tn`'s roots,
    the spent entries are live notes of `token`, and the nullifiers are fresh in tree
    `tn`. -/
def SpendEnabled (s : PoolState) (tn : Nat) (root : Term) (token : Token)
    (entries : List ((Nat × Nat) × CommitmentPreimage)) (nulls : List Term) : Prop :=
  root ∈ s.rootsAt' tn ∧
  (∃ rest, removeAll (s.live token) entries = some rest) ∧
  ∃ spent', markSpent (s.spent tn) nulls = some spent'

/-- The step from `s` to `s'` spends the note `e` of token `t`: `e` was live before the
    step and is not live after it. -/
def Spends (s s' : PoolState) (t : Token) (e : (Nat × Nat) × CommitmentPreimage) : Prop :=
  e ∈ s.live t ∧ e ∉ s'.live t

/--
**Non-interference: no step by any caller disables a pending spend, unless the step
spends one of the same notes.** Take a reachable state `s`, a spend of the live entries
`entries` of `token` in tree `tn`, with nullifiers `nullifier nk pos` derived from the
entries' positions, that is enabled at `s`. Then after any step `s → s'` (a shield, a
transact or an owned transact, by any caller) that spends none of `entries`, the same
spend is still enabled. Roots only accumulate (`step_rootsAt_shape`); a step removes
only the notes it spends (`removeAll_perm`); and a step marks only the nullifiers of the
positions it spends, which differ from the pending positions
(`live_positions_distinct_nullifiers`, `LiveSpentInvariant`). Replaces
`transact_cannot_be_blocked`/`transactOwned_cannot_be_blocked`, which covered only the
removed admin step (finding P-3). -/
theorem spend_not_blocked (s : ReachableState Pool.machine) {s' : PoolState} (hstep : Step s.state s')
    {tn : Nat} {root nk : Term} {token : Token}
    {entries : List ((Nat × Nat) × CommitmentPreimage)}
    (hTree : ∀ e ∈ entries, e.1.1 = tn)
    (hEnabled : SpendEnabled s.state tn root token entries (entries.map fun e => nullifier nk e.1.2))
    (hDisjoint : ∀ e ∈ entries, ¬ Spends s.state s' token e) :
    SpendEnabled s' tn root token entries (entries.map fun e => nullifier nk e.1.2) := by
  obtain_reach ⟨s, hs : Reachable s⟩ := s
  obtain ⟨hRoot, ⟨rest, hRemove⟩, spent', hNullify⟩ := hEnabled
  have hs' : Reachable s' := hs.step hstep
  have hRoot' : root ∈ s'.rootsAt' tn := by
    rcases step_rootsAt_shape hstep tn with heq | ⟨r, heq⟩
    · exact heq ▸ hRoot
    · exact heq ▸ List.mem_cons_of_mem r hRoot
  have hentries_s : ∀ e ∈ entries, e ∈ s.live token :=
    fun e he => (removeAll_perm hRemove).mem_iff.mpr (List.mem_append_left _ he)
  have hentries_s' : ∀ e ∈ entries, e ∈ s'.live token := by
    intro e he
    by_cases hmem : e ∈ s'.live token
    · exact hmem
    · exact absurd ⟨hentries_s e he, hmem⟩ (hDisjoint e he)
  have hNodupPool : (s.live token).Nodup :=
    (reachable_live_spent_invariant hs).2.2.2.2 token
  have hNodupPool' : (s'.live token).Nodup :=
    (reachable_live_spent_invariant hs').2.2.2.2 token
  have hentriesNodup : entries.Nodup := removeAll_wanted_nodup hNodupPool hRemove
  obtain ⟨rest', hRemove'⟩ := removeAll_of_subset hNodupPool' hentriesNodup hentries_s'
  obtain ⟨hnullsPairwise, _⟩ := owned_no_double_spend hNullify
  have hnullsFresh' : ∀ n ∈ entries.map (fun e => nullifier nk e.1.2), n ∉ s'.spent tn := by
    intro n hn
    obtain ⟨e, he, hen⟩ := List.mem_map.mp hn
    have heTn : e.1.1 = tn := hTree e he
    have heLive : e ∈ s'.live token := hentries_s' e he
    have hfresh := (reachable_live_spent_invariant hs').2.2.2.1 token e.1.1 e.1.2 e.2 heLive nk
    rw [heTn] at hfresh
    rw [← hen]
    exact hfresh
  obtain ⟨spent'', hNullify'⟩ := markSpent_succeeds hnullsPairwise hnullsFresh'
  exact ⟨hRoot', ⟨rest', hRemove'⟩, spent'', hNullify'⟩

/-- `spend_not_blocked` for a pending `Step.transact`: its state checks stay true across
    any step that spends none of its input notes.
    Source: TransactModule.sol:392-398 (pool symbolic types approval). -/
theorem transact_not_blocked (s : ReachableState Pool.machine) {s' : PoolState} (hstep : Step s.state s')
    {N M : Nat} {w : TransactWitness N M} {pub : TransactPublic N M} {bp : BoundParams}
    (hC : Constrained w pub)
    (hEnabled : SpendEnabled s.state bp.treeNumber pub.merkleRoot w.token
      (transactSpentPositions bp.treeNumber w) (List.ofFn pub.nullifiers))
    (hDisjoint : ∀ e ∈ transactSpentPositions bp.treeNumber w, ¬ Spends s.state s' w.token e) :
    SpendEnabled s' bp.treeNumber pub.merkleRoot w.token
      (transactSpentPositions bp.treeNumber w) (List.ofFn pub.nullifiers) := by
  obtain_reach ⟨s, hs : Reachable s⟩ := s
  have hnulls : List.ofFn pub.nullifiers =
      (transactSpentPositions bp.treeNumber w).map
        (fun e => nullifier (Term.val w.nullifyingKey) e.1.2) := by
    unfold transactSpentPositions
    rw [List.map_ofFn]
    congr 1
    funext i
    exact hC.nullifiers i
  have hTree : ∀ e ∈ transactSpentPositions bp.treeNumber w, e.1.1 = bp.treeNumber := by
    intro e he
    unfold transactSpentPositions at he
    obtain ⟨i, hi⟩ := List.mem_ofFn.mp he
    rw [← hi]
  rw [hnulls] at hEnabled ⊢
  exact spend_not_blocked ⟨_, (Pool.machine_reachable_iff.mpr hs)⟩ hstep hTree hEnabled hDisjoint

/-- `spend_not_blocked` for a pending `Step.transactOwned`: its state checks stay true
    across any step that spends none of its input notes.
    Source: TransactModule.sol:392-398 (plain-path mechanism; the owned path has
    no upstream equivalent, see the module header; pool symbolic types approval). -/
theorem transactOwned_not_blocked (s : ReachableState Pool.machine) {s' : PoolState} (hstep : Step s.state s')
    {N M : Nat} {w : TransactOwnedWitness N M} {pub : TransactOwnedPublic N M}
    {bp : BoundParams} (hC : OwnedConstrained w pub)
    (hEnabled : SpendEnabled s.state bp.treeNumber pub.merkleRoot w.token
      (ownedSpentPositions bp.treeNumber pub w) (List.ofFn pub.nullifiers))
    (hDisjoint : ∀ e ∈ ownedSpentPositions bp.treeNumber pub w, ¬ Spends s.state s' w.token e) :
    SpendEnabled s' bp.treeNumber pub.merkleRoot w.token
      (ownedSpentPositions bp.treeNumber pub w) (List.ofFn pub.nullifiers) := by
  obtain_reach ⟨s, hs : Reachable s⟩ := s
  have hnulls : List.ofFn pub.nullifiers =
      (ownedSpentPositions bp.treeNumber pub w).map
        (fun e => nullifier pub.ownerField e.1.2) := by
    unfold ownedSpentPositions
    rw [List.map_ofFn]
    congr 1
    funext i
    exact hC.nullifiers i
  have hTree : ∀ e ∈ ownedSpentPositions bp.treeNumber pub w, e.1.1 = bp.treeNumber := by
    intro e he
    unfold ownedSpentPositions at he
    obtain ⟨i, hi⟩ := List.mem_ofFn.mp he
    rw [← hi]
  rw [hnulls] at hEnabled ⊢
  exact spend_not_blocked ⟨_, (Pool.machine_reachable_iff.mpr hs)⟩ hstep hTree hEnabled hDisjoint

/-! ### A spend bound to an adapt contract (theorem 2 of the channel design) -/

/--
**Spend binding: a transaction bound to `(adaptContract, adaptParams)` executes only by
that contract and only with those parameters.** A proof fixes its public input
`boundHash`. If the bound parameters `bp₀` behind it name the adapt contract `a`, then
any step that executes the proof — `Step.transact` or `Step.transactOwned`, whose
`hBound` and `hAdapt` are the two hypotheses `hStep` and `hAdapt` here — has caller `a`
and bound parameters exactly `bp₀`, so the same `adaptParams` (the channel) and the
same unshield. A deposit spend therefore cannot be redirected to another contract or
another channel. The binding rests on `hashBoundParams_inj` (symbolic Keccak,
finding P-2) and on the adapt check (TransactModule.sol:530-532). -/
theorem spend_bound_to_adapt {boundHash : Term} {bp₀ bp : BoundParams} {a caller : Term}
    (hProof : boundHash = hashBoundParams bp₀) (hA : bp₀.adaptContract = some a)
    (hStep : boundHash = hashBoundParams bp) (hAdapt : AdaptAllows bp caller) :
    caller = a ∧ bp = bp₀ := by
  have heq : hashBoundParams bp₀ = hashBoundParams bp := hProof.symm.trans hStep
  have hbp : bp₀ = bp := hashBoundParams_inj heq
  rw [hbp] at hA
  exact ⟨hAdapt a hA, hbp.symm⟩

/-- Every entry recorded under `s.live t` in a reachable state carries token `t` in its
    own `CommitmentPreimage.token` field: the state's bookkeeping key and the note's own
    field never drift apart. True at every insertion site by construction
    (`Step.shield`'s `note`, `Step.transact`'s `newNotes` via `UnshieldRefines`/
    `unshieldRefines_mem`, `Step.transactOwned`'s `ownedNewNotes`, all built with the
    same token as the `live` key they are inserted under) and carried across the
    surviving `rest` of a spend by the induction hypothesis (`removeAll_perm`).
    `owned_merge_can_happen` needs this to carry a live note's claimed token into the
    circuit witness it builds from `hLive` alone, with no separate `hToken` hypothesis
    (unlike `owned_spend_witness_exists`, which is handed one). -/
theorem step_preserves_live_token {s s' : PoolState}
    (ih : ∀ t p, p ∈ s.live t → p.2.token = t) (hstep : Step s s') :
    ∀ t p, p ∈ s'.live t → p.2.token = t := by
  cases hstep with
  | setFeeRatio => exact ih
  | shield token x npk' hValue hSpendable =>
    intro t p hp
    by_cases ht : t = token
    · subst t
      simp only at hp
      rcases List.eq_or_mem_of_mem_cons hp with heq | hp
      · subst heq; rfl
      · exact ih token p hp
    · simp only [if_neg ht] at hp
      exact ih t p hp
  | transact caller w pub bp hN hM hC hBound hAdapt newNotes hOutputs rest spent' records
      openings hRoot hRemove hNullify hRecords =>
    intro t p hp
    by_cases ht : t = w.token
    · subst ht
      simp only at hp
      rcases List.mem_append.mp hp with hnew | hrest
      · have hqnew : p.2 ∈ newNotes := withTreePositionsFrom_snd_mem _ _ _ _ hnew
        have hmemall := unshieldRefines_mem hOutputs p.2 hqnew
        unfold transactAllOutputs at hmemall
        obtain ⟨j, hj⟩ := List.mem_ofFn.mp hmemall
        rw [← hj]
      · have hmemold : p ∈ s.live w.token :=
          (removeAll_perm hRemove).mem_iff.mpr (List.mem_append_right _ hrest)
        exact ih w.token p hmemold
    · simp only [if_neg ht] at hp
      exact ih t p hp
  | transactOwned w pub bp hN hM hC caller hCaller hBound hAdapt hNoUnshield rest spent'
      openings hRoot hRemove hNullify =>
    intro t p hp
    by_cases ht : t = w.token
    · subst ht
      simp only at hp
      rcases List.mem_append.mp hp with hnew | hrest
      · have hqnew : p.2 ∈ ownedNewNotes w := withTreePositionsFrom_snd_mem _ _ _ _ hnew
        unfold ownedNewNotes at hqnew
        obtain ⟨j, hj⟩ := List.mem_ofFn.mp hqnew
        rw [← hj]
      · have hmemold : p ∈ s.live w.token :=
          (removeAll_perm hRemove).mem_iff.mpr (List.mem_append_right _ hrest)
        exact ih w.token p hmemold
    · simp only [if_neg ht] at hp
      exact ih t p hp

theorem reachable_live_token {s : PoolState} (h : Reachable s) :
    ∀ t p, p ∈ s.live t → p.2.token = t := by
  induction h with
  | genesis _ _ _ => intro t p hp; (simp? [genesis] at hp says simp only [genesis, List.not_mem_nil] at hp)
  | step _ hstep ih => exact step_preserves_live_token ih hstep

/-! ### An owned merge (theorem 3 of the channel design) -/

/--
**Can happen: an owned transact merges several notes of one owner into one note.** In a
reachable state, take `N` (`1 ≤ N ≤ 8`) live notes of `token` at distinct positions of
tree `bp.treeNumber`, all owned by the address `owner` (`hOpen`: each note's `npk` is
`npk (Term.val owner) (random i)`). If the sum of their values passes the circuit's range check
(`hSum`), the owner can spend all of them in one `Step.transactOwned` with one output
of exactly that sum, to the note key `npkOut`. After the step none of the inputs is
live, the output is live, and the pool's custody of `token` is unchanged: value is
conserved. The witness comes from public data (`owned_spend_witness_exists`,
`live_leaf_matches`, `live_note_unspent`, `live_values_spendable`).

The deployed owned circuits have one input only (`main_{1x1,1x2,1x3}_owned.circom`).
The model's owned path admits `N ≤ 8`, so this theorem needs owned verifying keys with
`N > 1` at deployment.
Source: TransactModule.sol:488-519 (pool symbolic types approval). -/
theorem owned_merge_can_happen (s : ReachableState Pool.machine) {N : Nat}
    (hN0 : 0 < N) (hN : N ≤ 8)
    (owner : Address) (token : Token) (bp : BoundParams)
    (hNoUnshield : bp.unshield = none) (hAdapt : AdaptAllows bp (Term.val owner))
    (pos : Fin N → Nat) (pre : Fin N → CommitmentPreimage) (random : Fin N → Nat)
    (hLive : ∀ i, ((bp.treeNumber, pos i), pre i) ∈ s.state.live token)
    (hDistinct : (List.ofFn pos).Pairwise (· ≠ ·))
    (hOpen : ∀ i, npk (Term.val owner) (random i) = (pre i).npk)
    (npkOut : Term)
    (hSum : Spendable (listSum (List.ofFn fun i => (pre i).value))) :
    ∃ s', Step s.state s' ∧
      (∀ i, ((bp.treeNumber, pos i), pre i) ∉ s'.live token) ∧
      (∃ tn' pos' : Nat, ((tn', pos'),
        (⟨npkOut, token, listSum (List.ofFn fun i => (pre i).value)⟩ : CommitmentPreimage))
          ∈ s'.live token) ∧
      s'.held token = s.state.held token := by
  obtain_reach ⟨s, hs : Reachable s⟩ := s
  have hi0 : Fin N := ⟨0, hN0⟩
  have hLenLt : ∀ i, pos i < (s.leavesAt' bp.treeNumber).length := fun i =>
    (reachable_live_spent_invariant hs).1 token bp.treeNumber (pos i) (pre i) (hLive i)
  have hleavesNe : s.leavesAt' bp.treeNumber ≠ [] := by
    intro hnil; rw [hnil] at hLenLt; (simpa? using hLenLt hi0 says simpa only [List.length_nil, Nat.not_lt_zero] using hLenLt hi0)
  have hRootMem : treeRoot TreeDepth (s.leavesAt' bp.treeNumber) ∈ s.rootsAt' bp.treeNumber :=
    (reachable_rootAt_matches_leavesAt hs bp.treeNumber).resolve_left hleavesNe
  have hCap : (s.leavesAt' bp.treeNumber).length ≤ 2 ^ TreeDepth :=
    reachable_leavesAt_capacity hs bp.treeNumber
  have hLeafIndex : ∀ i, pos i < 2 ^ TreeDepth := fun i => by
    have h1 := hLenLt i
    omega
  have hLeafValue : ∀ i, (s.leavesAt' bp.treeNumber)[pos i]? = some (hashCommitment (pre i)) :=
    fun i => live_leaf_matches ⟨_, (Pool.machine_reachable_iff.mpr hs)⟩ token bp.treeNumber (pos i) (pre i) (hLive i)
  have hTokenEq : ∀ i, (pre i).token = token :=
    fun i => reachable_live_token hs token ((bp.treeNumber, pos i), pre i) (hLive i)
  have hSpendIn : ∀ i, RangeChecked120 (pre i).value :=
    fun i => live_values_spendable ⟨_, (Pool.machine_reachable_iff.mpr hs)⟩ token ((bp.treeNumber, pos i), pre i) (hLive i)
  have hFresh : ∀ i, nullifier (Term.val owner) (pos i) ∉ s.spent bp.treeNumber :=
    fun i => live_note_unspent ⟨_, (Pool.machine_reachable_iff.mpr hs)⟩ token bp.treeNumber (pos i) (pre i) (hLive i) (Term.val owner)
  let w : TransactOwnedWitness N 1 :=
    { token := token, randomIn := random,
      valueIn := fun i => (pre i).value,
      pathElements := fun i => treePath TreeDepth (s.leavesAt' bp.treeNumber) (pos i),
      leavesIndices := pos,
      npkOut := fun _ => npkOut,
      valueOut := fun _ => listSum (List.ofFn fun i => (pre i).value) }
  let pub : TransactOwnedPublic N 1 :=
    { merkleRoot := treeRoot TreeDepth (s.leavesAt' bp.treeNumber),
      boundParamsHash := hashBoundParams bp,
      nullifiers := fun i => nullifier (Term.val owner) (pos i),
      commitmentsOut := fun _ =>
        commitment npkOut token (listSum (List.ofFn fun i => (pre i).value)),
      owner := owner }
  have hConstrained : OwnedConstrained w pub :=
    { merkle := fun i => by
        have hcommit : commitment (npk (Term.val owner) (random i)) token ((pre i).value) =
            hashCommitment (pre i) := by
          unfold hashCommitment
          rw [hOpen i, hTokenEq i]
        show MerkleProof 16 (commitment (npk (Term.val owner) (random i)) token ((pre i).value))
            (treePath TreeDepth (s.leavesAt' bp.treeNumber) (pos i)) (pos i)
            (treeRoot TreeDepth (s.leavesAt' bp.treeNumber))
        rw [hcommit]
        exact treePath_merkleProof TreeDepth (s.leavesAt' bp.treeNumber) (pos i)
          (hLeafIndex i) (hLeafValue i)
      nullifiers := fun _ => rfl
      outputs := fun _ => rfl
      rangeIn := fun i => hSpendIn i
      rangeOut := fun _ => hSum
      balance := by
        have hBalanceEq : listSum (List.ofFn fun i => (pre i).value) =
            listSum (List.ofFn fun _ : Fin 1 =>
              listSum (List.ofFn fun i => (pre i).value)) := by
          (simp? [listSum] says simp only [List.ofFn_succ, List.ofFn_zero, listSum, Nat.add_zero])
        exact congrArg (· % p) hBalanceEq }
  have hwantedEq : (List.ofFn fun i => ((bp.treeNumber, pos i), pre i) :
      List ((Nat × Nat) × CommitmentPreimage)) = ownedSpentPositions bp.treeNumber pub w := by
    unfold ownedSpentPositions
    congr 1
    funext i
    have hval : (⟨npk (Term.val owner) (random i), token, (pre i).value⟩ : CommitmentPreimage) = pre i := by
      rw [hOpen i, ← hTokenEq i]
    show ((bp.treeNumber, pos i), pre i) =
      ((bp.treeNumber, pos i),
        (⟨npk (Term.val owner) (random i), token, (pre i).value⟩ : CommitmentPreimage))
    rw [hval]
  have hwantedPairwise :
      (List.ofFn fun i => ((bp.treeNumber, pos i), pre i) :
        List ((Nat × Nat) × CommitmentPreimage)).Pairwise (· ≠ ·) := by
    rw [List.pairwise_iff_getElem]
    simp only [List.length_ofFn, List.getElem_ofFn]
    intro a b ha hb hab heq
    have hposeq : pos ⟨a, ha⟩ = pos ⟨b, hb⟩ := congrArg (fun p => p.1.2) heq
    have hine : (⟨a, ha⟩ : Fin N) ≠ ⟨b, hb⟩ := fun hc => by
      have hc' := congrArg Fin.val hc
      simp only at hc'
      omega
    exact ofFn_pairwise_ne pos hDistinct ⟨a, ha⟩ ⟨b, hb⟩ hine hposeq
  have hsub : ∀ e ∈ (List.ofFn fun i => ((bp.treeNumber, pos i), pre i) :
      List ((Nat × Nat) × CommitmentPreimage)), e ∈ s.live token := by
    intro e he
    obtain ⟨i, hi⟩ := List.mem_ofFn.mp he
    rw [← hi]; exact hLive i
  have hpoolNodup : (s.live token).Nodup := (reachable_live_spent_invariant hs).2.2.2.2 token
  obtain ⟨rest, hRemovePre⟩ := removeAll_of_subset hpoolNodup hwantedPairwise hsub
  have hRemove :
      removeAll (s.live w.token) (ownedSpentPositions bp.treeNumber pub w) = some rest := by
    rw [← hwantedEq]; exact hRemovePre
  obtain ⟨spent', hNullify⟩ :
      ∃ spent', markSpent (s.spent bp.treeNumber) (List.ofFn pub.nullifiers) = some spent' := by
    apply markSpent_succeeds
    · have hmap := distinct_leaves_distinct_nullifiers (Term.val owner) (List.ofFn pos) hDistinct
      have heq2 : (List.ofFn pos).map (nullifier (Term.val owner)) = List.ofFn pub.nullifiers :=
        List.map_ofFn
      rwa [heq2] at hmap
    · intro n hn
      obtain ⟨i, hi⟩ := List.mem_ofFn.mp hn
      rw [← hi]
      exact hFresh i
  refine ⟨_, Step.transactOwned w pub bp hN (by omega) hConstrained (Term.val owner) rfl rfl hAdapt
    hNoUnshield rest spent' [] hRootMem hRemove hNullify, ?_, ?_, rfl⟩
  · intro i
    show ((bp.treeNumber, pos i), pre i) ∉
      (if token = w.token then
        withTreePositionsFrom (insertTree s.trees (ownedNewNotes w).length)
          (insertStart s.trees (ownedNewNotes w).length) (ownedNewNotes w) ++ rest
      else s.live token)
    rw [if_pos rfl]
    intro hmem
    rcases List.mem_append.mp hmem with hnew | hrest
    · have htn := withTreePositionsFrom_treeNumber
        (insertTree s.trees (ownedNewNotes w).length)
        (insertStart s.trees (ownedNewNotes w).length) (ownedNewNotes w) _ hnew
      have hge := withTreePositionsFrom_pos_ge
        (insertTree s.trees (ownedNewNotes w).length)
        (insertStart s.trees (ownedNewNotes w).length) (ownedNewNotes w) _ hnew
      simp only at htn hge
      have hpos0eq := insertStart_eq s.trees (ownedNewNotes w).length
      rw [← htn] at hpos0eq
      have hlt : pos i < insertStart s.trees (ownedNewNotes w).length := by
        rw [hpos0eq]; exact hLenLt i
      omega
    · have hwmem : ((bp.treeNumber, pos i), pre i) ∈ ownedSpentPositions bp.treeNumber pub w := by
        rw [← hwantedEq]; exact List.mem_ofFn.mpr ⟨i, rfl⟩
      exact (removeAll_disjoint hpoolNodup hRemove) _ hwmem hrest
  · refine ⟨insertTree s.trees (ownedNewNotes w).length,
      insertStart s.trees (ownedNewNotes w).length, ?_⟩
    show ((insertTree s.trees (ownedNewNotes w).length,
        insertStart s.trees (ownedNewNotes w).length),
        (⟨npkOut, token, listSum (List.ofFn fun i => (pre i).value)⟩ : CommitmentPreimage)) ∈
      (if token = w.token then
        withTreePositionsFrom (insertTree s.trees (ownedNewNotes w).length)
          (insertStart s.trees (ownedNewNotes w).length) (ownedNewNotes w) ++ rest
      else s.live token)
    rw [if_pos rfl]
    apply List.mem_append_left
    have hone : ownedNewNotes w =
        [(⟨npkOut, token, listSum (List.ofFn fun i => (pre i).value)⟩ : CommitmentPreimage)] := by
      show (List.ofFn fun _ : Fin 1 =>
          (⟨npkOut, token, listSum (List.ofFn fun i => (pre i).value)⟩ : CommitmentPreimage)) = _
      (simp? says simp only [List.ofFn_succ, List.ofFn_zero])
    rw [hone]
    unfold withTreePositionsFrom withPositionsFrom
    (simp? says simp only [List.length_cons, List.length_nil, Nat.zero_add, List.map_cons, List.mem_cons, List.mem_map, Prod.mk.injEq, true_and, Prod.exists, exists_eq_right_right, exists_eq_right, true_or])

/-! ### Refinement between `Pool.apply` and `Step` (docs/pool-executable.md, rules PE4
and PE5) -/

/-- **Forward refinement** (rule PE4): `Pool.apply` simulates
every `Step`.

For every reachable state and every model transition, some call makes `Pool.apply`
compute the contract state the transition reaches. The hypothesis — `verify` accepts
every proof for public inputs a witness satisfies — is the completeness of the trusted
verifier: `TransactProofCompleteness`/`OwnedProofCompleteness` give that a `Constrained`/
`OwnedConstrained` witness's public input is accepted by the model's own
`VerifyAccepts`/`VerifyOwnedAccepts`, and `Pool.Verifier.Realizes` carries that over to
`verify` itself. The shield case reuses `Step.shield`'s own hypotheses directly
(`ShieldPre` is stated to match them exactly); the transact cases reuse `Step.transact`'s/
`Step.transactOwned`'s `Constrained`/`OwnedConstrained` witness to pick the call's proof,
unshield token and disclosed records.

Source: docs/pool-executable.md rule PE4 (design decision 2026-11-04). -/
theorem Pool.apply_forward_refinement (verify : Pool.Verifier) (hReal : verify.Realizes)
    (hT : TransactProofCompleteness) (hO : OwnedProofCompleteness)
    (rs : ReachableState Pool.machine) {s' : PoolState} (h : Step rs.state s') :
    ∃ c : Pool.Call, Pool.apply verify rs.state.contract c = some s'.contract := by
  cases h with
  | shield token x npk hValue hSpendable =>
    refine ⟨.shield token x npk, ?_⟩
    have hPre : rs.state.contract.ShieldPre token x npk :=
      ⟨hValue, rangeCheck120_sound _ hSpendable⟩
    rw [Pool.apply_shield_equation, dif_pos hPre]
    rfl
  | transact caller w pub bp hN hM hC hBound hAdapt newNotes hOutputs rest spent'
      records openings hRoot hRemove hNullify hRecords =>
    obtain ⟨proof, hproof⟩ := (hReal.transact pub).mp (hT.complete hC)
    have hCommitmentsOut :
        List.ofFn pub.commitmentsOut = (transactAllOutputs w).map hashCommitment := by
      rw [transactAllOutputs, List.map_ofFn]
      exact congrArg List.ofFn (funext fun j => hC.outputs j)
    have hRecordsMatch : recordsMatch pub.commitmentsOut records = true := by
      unfold recordsMatch
      rw [List.all_eq_true]
      rintro ⟨c1, c2⟩ hcp
      obtain ⟨j, hj⟩ := List.mem_ofFn.mp (hRecords.subset hcp)
      injection hj with hj1 hj2
      subst hj1; subst hj2
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨(hC.outputs j).symm, List.elem_eq_true_of_mem (List.mem_ofFn.mpr ⟨j, rfl⟩)⟩
    have hIsSome :
        (markSpent (rs.state.contract.spent bp.treeNumber) (List.ofFn pub.nullifiers)).isSome
          = true := by
      show (markSpent (rs.state.spent bp.treeNumber) (List.ofFn pub.nullifiers)).isSome = true
      rw [hNullify]; rfl
    have hSpent :
        (fun n => if n = bp.treeNumber then
            (markSpent (rs.state.spent bp.treeNumber) (List.ofFn pub.nullifiers)).getD
              (rs.state.spent bp.treeNumber)
          else rs.state.spent n) = (fun n => if n = bp.treeNumber then spent' else rs.state.spent n) := by
      funext n
      simp only [hNullify, Option.getD_some]
    rcases hu : bp.unshield with _ | u
    · refine ⟨.transact caller pub bp proof none records openings, ?_⟩
      have hNoneOutputs : transactAllOutputs w = newNotes := by
        unfold UnshieldRefines at hOutputs; rw [hu] at hOutputs; exact hOutputs
      have hTrees : insertLeaves rs.state.trees (List.ofFn pub.commitmentsOut) =
          insertLeaves rs.state.trees (newNotes.map hashCommitment) := by
        rw [hCommitmentsOut, hNoneOutputs]
      have hPre : rs.state.contract.TransactPre verify caller pub bp proof none records openings :=
        ⟨hN, hM, hproof, hBound, hAdapt, hRoot, hIsSome, hRecordsMatch, by
          simp [unshieldCommitted, hu]⟩
      rw [Pool.apply_transact_equation, dif_pos hPre]
      congr 1
      unfold Pool.ContractState.transactEffect PoolState.contract
      simp [hTrees, hSpent, withdrawn]
    · refine ⟨.transact caller pub bp proof (some w.token) records openings, ?_⟩
      have hSomeOutputs :
          transactAllOutputs w = newNotes ++ [(⟨u.recipient, w.token, u.value⟩ : CommitmentPreimage)] := by
        unfold UnshieldRefines at hOutputs; rw [hu] at hOutputs; exact hOutputs
      have hLast :
          (List.ofFn pub.commitmentsOut).getLast? =
            some (hashCommitment ⟨u.recipient, w.token, u.value⟩) := by
        rw [hCommitmentsOut, hSomeOutputs, List.map_append, List.map_singleton]
        exact List.getLast?_concat
      have hTrees : insertLeaves rs.state.trees ((List.ofFn pub.commitmentsOut).dropLast) =
          insertLeaves rs.state.trees (newNotes.map hashCommitment) := by
        rw [hCommitmentsOut, hSomeOutputs, List.map_append, List.map_singleton, List.dropLast_concat]
      have hPre :
          rs.state.contract.TransactPre verify caller pub bp proof (some w.token) records openings :=
        ⟨hN, hM, hproof, hBound, hAdapt, hRoot, hIsSome, hRecordsMatch, by
          simp only [unshieldCommitted, hu, decide_eq_true_eq]; exact hLast⟩
      rw [Pool.apply_transact_equation, dif_pos hPre]
      congr 1
      unfold Pool.ContractState.transactEffect PoolState.contract
      dsimp only
      rw [hTrees, hSpent, hu]
  | transactOwned w pub bp hN hM hC caller hCaller hBound hAdapt hNoUnshield rest spent'
      openings hRoot hRemove hNullify =>
    obtain ⟨proof, hproof⟩ := (hReal.owned pub).mp (hO.complete hC)
    refine ⟨.transactOwned caller pub bp proof (ownedOutputRecords w pub) openings, ?_⟩
    have hCommitmentsOut :
        List.ofFn pub.commitmentsOut = (ownedNewNotes w).map hashCommitment := by
      rw [ownedNewNotes, List.map_ofFn]
      exact congrArg List.ofFn (funext fun j => hC.outputs j)
    have hRecordsComplete :
        recordsComplete pub.commitmentsOut (ownedOutputRecords w pub) = true := by
      unfold recordsComplete ownedOutputRecords outputRecords
      rw [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
      constructor
      · rw [List.map_ofFn]
        exact congrArg List.ofFn (funext fun _ => rfl)
      · rintro ⟨c1, c2⟩ hcp
        obtain ⟨j, hj⟩ := List.mem_ofFn.mp hcp
        injection hj with hj1 hj2
        subst hj1; subst hj2
        exact decide_eq_true (hC.outputs j).symm
    have hIsSome :
        (markSpent (rs.state.contract.spent bp.treeNumber) (List.ofFn pub.nullifiers)).isSome
          = true := by
      show (markSpent (rs.state.spent bp.treeNumber) (List.ofFn pub.nullifiers)).isSome = true
      rw [hNullify]; rfl
    have hSpent :
        (fun n => if n = bp.treeNumber then
            (markSpent (rs.state.spent bp.treeNumber) (List.ofFn pub.nullifiers)).getD
              (rs.state.spent bp.treeNumber)
          else rs.state.spent n) = (fun n => if n = bp.treeNumber then spent' else rs.state.spent n) := by
      funext n
      simp only [hNullify, Option.getD_some]
    have hTrees : insertLeaves rs.state.trees (List.ofFn pub.commitmentsOut) =
        insertLeaves rs.state.trees ((ownedNewNotes w).map hashCommitment) := by
      rw [hCommitmentsOut]
    have hPre :
        rs.state.contract.TransactOwnedPre verify caller pub bp proof
          (ownedOutputRecords w pub) openings :=
      ⟨hN, hM, hCaller, hproof, hBound, hAdapt, hNoUnshield, hRoot, hIsSome, hRecordsComplete⟩
    rw [Pool.apply_transactOwned_equation, dif_pos hPre]
    congr 1
    unfold Pool.ContractState.transactOwnedEffect PoolState.contract
    dsimp only
    rw [hTrees, hSpent]
  | setFeeRatio caller hCaller r =>
    refine ⟨.setFeeRatio caller r, ?_⟩
    rw [Pool.apply_setFeeRatio_equation,
      dif_pos (show rs.state.contract.SetFeeRatioPre caller r from hCaller)]
    rfl

/-! ### The inputs of an accepted proof are live -/

/-- The spent positions of a `Constrained` witness are live when the root is in the
    tree's history and the nullifiers are fresh. Each input opens, along its path, a
    leaf of the tree (`roots_of_prefixes`, `MerkleProof.opens_treeRoot`). The leaf is
    live or its note is spent (`leaf_live_or_spent`). A spent note's nullifier key is
    the witness's own nullifying key (a user key is never an owner field,
    `Term.val_ne_hash`), and that nullifier is fresh. So every input is live, and the
    nullifiers' distinctness makes the positions distinct. -/
theorem transact_inputs_live (s : ReachableState Pool.machine) {N M : Nat}
    {w : TransactWitness N M} {pub : TransactPublic N M} (hC : Constrained w pub) (tn : Nat)
    (hRoot : pub.merkleRoot ∈ s.state.rootsAt' tn) {spent' : NullifierSet}
    (hNullify : markSpent (s.state.spent tn) (List.ofFn pub.nullifiers) = some spent') :
    ∃ rest, removeAll (s.state.live w.token) (transactSpentPositions tn w) = some rest := by
  have hs : Reachable s.state := Pool.machine_reachable_iff.mp s.reachable
  obtain ⟨hpw, hfresh⟩ := owned_no_double_spend hNullify
  have hne := ofFn_pairwise_ne pub.nullifiers hpw
  refine removeAll_of_subset ((reachable_live_spent_invariant hs).2.2.2.2 w.token) ?_ ?_
  · refine ofFn_nodup_of_ne _ fun i j hij heq => hne i j hij ?_
    rw [hC.nullifiers i, hC.nullifiers j]
    simp only [Prod.mk.injEq] at heq
    rw [heq.1.2]
  · intro e he
    obtain ⟨i, hi⟩ := List.mem_ofFn.mp he
    subst hi
    obtain ⟨ls, ⟨tl, htl⟩, hr⟩ := (roots_of_prefixes s).roots tn _ hRoot
    have hm := hC.merkle i
    rw [hr] at hm
    have hget := MerkleProof.opens_treeRoot hm
    have hsome := List.getElem?_eq_some_of_getD ls _ emptyLeaf (by
      rw [hget]
      exact Ne.symm (emptyLeaf_ne_hashCommitment ⟨npk (masterPublicKey w.publicKey w.nullifyingKey)
        (w.randomIn i), w.token, w.valueIn i⟩))
    rw [hget] at hsome
    obtain ⟨hlt, _⟩ := List.getElem?_eq_some_iff.mp hsome
    have hleaf : (s.state.leavesAt' tn)[w.leavesIndices i]? = some (hashCommitment
        ⟨npk (masterPublicKey w.publicKey w.nullifyingKey) (w.randomIn i), w.token,
          w.valueIn i⟩) := by
      rw [← htl, List.getElem?_append_left hlt]
      exact hsome
    rcases (leaf_live_or_spent s).leaf tn _ _ hleaf with hlv | ⟨nk, hkey, hsp⟩
    · exact hlv
    · exfalso
      rcases hkey with ⟨pk, k, r, hnpk, hnk⟩ | ⟨o, r, hnpk, hnk⟩
      · have hmpk := (Term.hash2_inj hnpk).1
        have hk : Term.val w.nullifyingKey = Term.val k := (Term.hash3_inj hmpk).2.2
        rw [hnk, ← hk, ← hC.nullifiers i] at hsp
        exact hfresh _ (List.mem_ofFn.mpr ⟨i, rfl⟩) hsp
      · have hmpk := (Term.hash2_inj hnpk).1
        exact Term.val_ne_hash o _ _ hmpk.symm

/-- The owned counterpart of `transact_inputs_live`. A spent note's nullifier key is the
    owner field itself (an owner field is never a master public key,
    `TransactOwnedPublic.ownerField_ne_hash`). -/
theorem transactOwned_inputs_live (s : ReachableState Pool.machine) {N M : Nat}
    {w : TransactOwnedWitness N M} {pub : TransactOwnedPublic N M} (hC : OwnedConstrained w pub)
    (tn : Nat) (hRoot : pub.merkleRoot ∈ s.state.rootsAt' tn) {spent' : NullifierSet}
    (hNullify : markSpent (s.state.spent tn) (List.ofFn pub.nullifiers) = some spent') :
    ∃ rest, removeAll (s.state.live w.token) (ownedSpentPositions tn pub w) = some rest := by
  have hs : Reachable s.state := Pool.machine_reachable_iff.mp s.reachable
  obtain ⟨hpw, hfresh⟩ := owned_no_double_spend hNullify
  have hne := ofFn_pairwise_ne pub.nullifiers hpw
  refine removeAll_of_subset ((reachable_live_spent_invariant hs).2.2.2.2 w.token) ?_ ?_
  · refine ofFn_nodup_of_ne _ fun i j hij heq => hne i j hij ?_
    rw [hC.nullifiers i, hC.nullifiers j]
    simp only [Prod.mk.injEq] at heq
    rw [heq.1.2]
  · intro e he
    obtain ⟨i, hi⟩ := List.mem_ofFn.mp he
    subst hi
    obtain ⟨ls, ⟨tl, htl⟩, hr⟩ := (roots_of_prefixes s).roots tn _ hRoot
    have hm := hC.merkle i
    rw [hr] at hm
    have hget := MerkleProof.opens_treeRoot hm
    have hsome := List.getElem?_eq_some_of_getD ls _ emptyLeaf (by
      rw [hget]
      exact Ne.symm (emptyLeaf_ne_hashCommitment ⟨npk pub.ownerField (w.randomIn i), w.token,
        w.valueIn i⟩))
    rw [hget] at hsome
    obtain ⟨hlt, _⟩ := List.getElem?_eq_some_iff.mp hsome
    have hleaf : (s.state.leavesAt' tn)[w.leavesIndices i]? = some (hashCommitment
        ⟨npk pub.ownerField (w.randomIn i), w.token, w.valueIn i⟩) := by
      rw [← htl, List.getElem?_append_left hlt]
      exact hsome
    rcases (leaf_live_or_spent s).leaf tn _ _ hleaf with hlv | ⟨nk, hkey, hsp⟩
    · exact hlv
    · exfalso
      rcases hkey with ⟨pk, k, r, hnpk, hnk⟩ | ⟨o, r, hnpk, hnk⟩
      · have hmpk := (Term.hash2_inj hnpk).1
        exact pub.ownerField_ne_hash _ _ hmpk
      · have ho : pub.ownerField = Term.val o := (Term.hash2_inj hnpk).1
        rw [hnk, ← ho, ← hC.nullifiers i] at hsp
        exact hfresh _ (List.mem_ofFn.mpr ⟨i, rfl⟩) hsp

/-! ### The records of an accepted call -/

/-- The records a plain `transact` call discloses (`recordsMatch`) give the registry of
    some sublist of the witness's own output records: the sublist of the records the
    call names. Every disclosed record is one of the witness's output records, so the
    two lists name one set of commitments (`applyRecords_eq_of_keys`). -/
theorem transact_records_registry {N M : Nat} {w : TransactWitness N M}
    {pub : TransactPublic N M} (hC : Constrained w pub)
    {records : List (Term × CommitmentPreimage)}
    (hMatch : recordsMatch pub.commitmentsOut records = true) (reg : PreimageRegistry) :
    ∃ records' : List (Term × CommitmentPreimage),
      records'.Sublist (transactOutputRecords w pub) ∧
      applyRecords reg records' = applyRecords reg records := by
  have hmem : ∀ cp ∈ records, cp ∈ transactOutputRecords w pub := by
    intro cp hcp
    obtain ⟨c, p⟩ := cp
    unfold recordsMatch at hMatch
    have h := List.all_eq_true.mp hMatch (c, p) hcp
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨hhash, hmem⟩ := h
    obtain ⟨j, hj⟩ := List.mem_ofFn.mp (List.mem_of_elem_eq_true hmem)
    have hpre : p = ⟨w.npkOut j, w.token, w.valueOut j⟩ :=
      hashCommitment_inj (hhash.trans (hj.symm.trans (hC.outputs j)))
    subst hj
    subst hpre
    exact List.mem_ofFn.mpr ⟨j, rfl⟩
  refine ⟨(transactOutputRecords w pub).filter (fun cp => decide (cp ∈ records)),
    List.filter_sublist, ?_⟩
  apply applyRecords_eq_of_keys
  · exact ⟨fun cp hcp => transactOutputRecords_valid hC cp (List.mem_filter.mp hcp).1⟩
  · refine ⟨fun cp hcp => ?_⟩
    have h := List.all_eq_true.mp hMatch cp hcp
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact h.1
  · intro c
    constructor
    · intro hc
      obtain ⟨cp, hcp, hc⟩ := List.mem_map.mp hc
      exact List.mem_map.mpr ⟨cp, (List.mem_filter.mp hcp).2 |> of_decide_eq_true, hc⟩
    · intro hc
      obtain ⟨cp, hcp, hc⟩ := List.mem_map.mp hc
      exact List.mem_map.mpr ⟨cp, List.mem_filter.mpr ⟨hmem cp hcp, decide_eq_true hcp⟩, hc⟩

/-- The records an owned call discloses (`recordsComplete`) give the registry of the
    witness's own output records: the two lists name the output commitments in order. -/
theorem transactOwned_records_registry {N M : Nat} {w : TransactOwnedWitness N M}
    {pub : TransactOwnedPublic N M} (hC : OwnedConstrained w pub)
    {records : List (Term × CommitmentPreimage)}
    (hComplete : recordsComplete pub.commitmentsOut records = true) (reg : PreimageRegistry) :
    applyRecords reg (ownedOutputRecords w pub) = applyRecords reg records := by
  unfold recordsComplete at hComplete
  rw [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hComplete
  obtain ⟨hkeys, hvalid⟩ := hComplete
  apply applyRecords_eq_of_keys
  · exact ⟨ownedOutputRecords_valid hC⟩
  · exact ⟨fun cp hcp => of_decide_eq_true (hvalid cp hcp)⟩
  · intro c
    rw [hkeys]
    unfold ownedOutputRecords outputRecords
    rw [List.map_ofFn]
    rfl

/-- **Backward refinement** (rule PE5): every call that
`Pool.apply` accepts is the contract image of some `Step`.

For every reachable state, when `Pool.apply` accepts a call and computes `t`, some model
transition from that state reaches a state whose contract image is `t`. The hypothesis —
every public input that `verify` accepts has a witness that satisfies the circuit — is
the soundness of the trusted verifier: `TransactProofSoundness`/`OwnedProofSoundness`
give a `Constrained`/`OwnedConstrained` witness for every public input the model's own
`VerifyAccepts`/`VerifyOwnedAccepts` accepts, and `Pool.Verifier.Realizes` carries that
over to `verify` itself. Reachability is needed: the contract checks nullifier freshness
and the Merkle root, while `Step.transact` checks that the spent positions are live
(`hRemove`); `live_note_unspent` and `live_leaf_matches` tie the two on reachable states.

Source: docs/pool-executable.md rule PE5 (design decision 2026-11-04). -/
theorem Pool.apply_backward_refinement (verify : Pool.Verifier) (hReal : verify.Realizes)
    (hTS : TransactProofSoundness) (hOS : OwnedProofSoundness)
    (s : ReachableState Pool.machine) {c : Pool.Call} {t : Pool.ContractState}
    (h : Pool.apply verify s.state.contract c = some t) :
    ∃ s' : PoolState, Step s.state s' ∧ s'.contract = t := by
  cases c with
  | shield token x npk =>
    rw [Pool.apply_shield_equation] at h
    by_cases hPre : s.state.contract.ShieldPre token x npk
    · rw [dif_pos hPre] at h
      obtain ⟨hValue, hBound⟩ := hPre
      refine ⟨_, Step.shield token x npk hValue (spendable_of_lt hBound), ?_⟩
      rw [← Option.some.inj h]
      rfl
    · rw [dif_neg hPre] at h
      exact absurd h (by (simp? says simp only [reduceCtorEq, not_false_eq_true]))
  | setFeeRatio caller r =>
    rw [Pool.apply_setFeeRatio_equation] at h
    by_cases hPre : s.state.contract.SetFeeRatioPre caller r
    · rw [dif_pos hPre] at h
      refine ⟨_, Step.setFeeRatio caller hPre r, ?_⟩
      rw [← Option.some.inj h]
      rfl
    · rw [dif_neg hPre] at h
      exact absurd h (by (simp? says simp only [reduceCtorEq, not_false_eq_true]))
  | transact caller pub bp proof unshieldToken records openings =>
    rw [Pool.apply_transact_equation] at h
    by_cases hPre : s.state.contract.TransactPre verify caller pub bp proof unshieldToken
        records openings
    · rw [dif_pos hPre] at h
      have ht := Option.some.inj h
      clear h
      obtain ⟨hN, hM, hproof, hBound, hAdapt, hRoot, hIsSome, hRecordsMatch, hUnshield⟩ := hPre
      obtain ⟨w, hC⟩ := hTS.sound ((hReal.transact pub).mpr ⟨proof, hproof⟩)
      obtain ⟨spent', hNullify⟩ := Option.isSome_iff_exists.mp hIsSome
      obtain ⟨rest, hRemove⟩ := transact_inputs_live s hC bp.treeNumber hRoot hNullify
      obtain ⟨records', hRecords, hReg⟩ :=
        transact_records_registry hC hRecordsMatch s.state.preimageOf
      have hCommitmentsOut :
          List.ofFn pub.commitmentsOut = (transactAllOutputs w).map hashCommitment := by
        rw [transactAllOutputs, List.map_ofFn]
        exact congrArg List.ofFn (funext fun j => hC.outputs j)
      have hSpent :
          (fun n => if n = bp.treeNumber then spent' else s.state.spent n) =
          (fun n => if n = bp.treeNumber then
              (markSpent (s.state.spent bp.treeNumber) (List.ofFn pub.nullifiers)).getD
                (s.state.spent bp.treeNumber)
            else s.state.spent n) := by
        funext n
        have hNullify' :
            markSpent (s.state.spent bp.treeNumber) (List.ofFn pub.nullifiers) = some spent' :=
          hNullify
        simp only [hNullify', Option.getD_some]
      cases unshieldToken with
      | none =>
        unfold Pool.ContractState.transactEffect at ht
        dsimp only at ht
        subst ht
        rcases hu : bp.unshield with _ | u
        · refine ⟨_, Step.transact caller w pub bp hN hM hC hBound hAdapt (transactAllOutputs w)
            (by show UnshieldRefines w bp.unshield _; rw [hu]; exact rfl)
            rest spent' records' openings hRoot hRemove hNullify hRecords, ?_⟩
          unfold PoolState.contract
          dsimp only
          rw [hCommitmentsOut, hSpent, hReg]
          congr 1
          funext t
          simp only [withdrawn, hu, Nat.sub_zero, ite_self]
        · exfalso
          rw [hu] at hUnshield
          dsimp only [unshieldCommitted] at hUnshield
          exact Bool.false_ne_true hUnshield
      | some tok =>
        unfold Pool.ContractState.transactEffect at ht
        dsimp only at ht
        subst ht
        rcases hu : bp.unshield with _ | u
        · exfalso
          rw [hu] at hUnshield
          dsimp only [unshieldCommitted] at hUnshield
          exact Bool.false_ne_true hUnshield
        · rw [hu] at hUnshield
          dsimp only [unshieldCommitted] at hUnshield
          rw [decide_eq_true_eq, hCommitmentsOut, List.getLast?_map] at hUnshield
          cases hlast : (transactAllOutputs w).getLast? with
          | none =>
            rw [hlast] at hUnshield
            exact absurd hUnshield (by (simp? says simp only [Option.map_none, reduceCtorEq, not_false_eq_true]))
          | some last =>
            rw [hlast] at hUnshield
            simp only [Option.map_some, Option.some.injEq] at hUnshield
            have hlastEq : last = ⟨u.recipient, tok, u.value⟩ := hashCommitment_inj hUnshield
            obtain ⟨l', hl'⟩ := List.getLast?_eq_some_iff.mp hlast
            have htok : tok = w.token := by
              have hmem : last ∈ transactAllOutputs w := by
                rw [hl']; exact List.mem_append_right _ List.mem_cons_self
              obtain ⟨j, hj⟩ := List.mem_ofFn.mp hmem
              have := congrArg CommitmentPreimage.token hj
              rw [hlastEq] at this
              exact this.symm
            subst htok
            subst hlastEq
            refine ⟨_, Step.transact caller w pub bp hN hM hC hBound hAdapt l'
              (by show UnshieldRefines w bp.unshield _; rw [hu]; exact hl')
              rest spent' records' openings hRoot hRemove hNullify hRecords, ?_⟩
            unfold PoolState.contract
            dsimp only
            rw [hCommitmentsOut, hl', List.map_append, List.map_singleton, List.dropLast_concat,
              hSpent, hReg, hu]
    · rw [dif_neg hPre] at h
      exact absurd h (by (simp? says simp only [reduceCtorEq, not_false_eq_true]))
  | transactOwned caller pub bp proof records openings =>
    rw [Pool.apply_transactOwned_equation] at h
    by_cases hPre : s.state.contract.TransactOwnedPre verify caller pub bp proof records openings
    · rw [dif_pos hPre] at h
      obtain ⟨hN, hM, hCaller, hproof, hBound, hAdapt, hNoUnshield, hRoot, hIsSome,
        hRecordsComplete⟩ := hPre
      obtain ⟨w, hC⟩ := hOS.sound ((hReal.owned pub).mpr ⟨proof, hproof⟩)
      obtain ⟨spent', hNullify⟩ := Option.isSome_iff_exists.mp hIsSome
      obtain ⟨rest, hRemove⟩ := transactOwned_inputs_live s hC bp.treeNumber hRoot hNullify
      have hCommitmentsOut :
          List.ofFn pub.commitmentsOut = (ownedNewNotes w).map hashCommitment := by
        rw [ownedNewNotes, List.map_ofFn]
        exact congrArg List.ofFn (funext fun j => hC.outputs j)
      have hSpent :
          (fun n => if n = bp.treeNumber then spent' else s.state.spent n) =
          (fun n => if n = bp.treeNumber then
              (markSpent (s.state.spent bp.treeNumber) (List.ofFn pub.nullifiers)).getD
                (s.state.spent bp.treeNumber)
            else s.state.spent n) := by
        funext n
        have hNullify' :
            markSpent (s.state.spent bp.treeNumber) (List.ofFn pub.nullifiers) = some spent' :=
          hNullify
        simp only [hNullify', Option.getD_some]
      refine ⟨_, Step.transactOwned w pub bp hN hM hC caller hCaller hBound hAdapt hNoUnshield
        rest spent' openings hRoot hRemove hNullify, ?_⟩
      rw [← Option.some.inj h]
      unfold Pool.ContractState.transactOwnedEffect PoolState.contract
      dsimp only
      rw [hCommitmentsOut, hSpent, transactOwned_records_registry hC hRecordsComplete]
    · rw [dif_neg hPre] at h
      exact absurd h (by (simp? says simp only [reduceCtorEq, not_false_eq_true]))
/-- The induction step of `Pool.apply_backward_refinement_run` (rule PE7): `Pool.applyRun`
applies `Pool.apply_backward_refinement` (rule PE5) at each call of the list, from any reachable
state rather than only `genesis`, carrying reachability one `Step` forward at a time. -/
theorem Pool.applyRun_reaches_contract (verify : Pool.Verifier) (hReal : verify.Realizes)
    (hTS : TransactProofSoundness) (hOS : OwnedProofSoundness) :
    ∀ (cs : List Pool.Call) (s : ReachableState Pool.machine) {t : Pool.ContractState},
      Pool.applyRun verify s.state.contract cs = some t →
      ∃ s' : PoolState, Reachable s' ∧ s'.contract = t
  | [], s, t, h => ⟨s.state, Pool.machine_reachable_iff.mp s.reachable, Option.some.inj h⟩
  | c :: cs, s, t, h => by
      rw [Pool.applyRun_cons] at h
      cases hb : Pool.apply verify s.state.contract c with
      | none => rw [hb] at h; exact absurd h (by simp)
      | some t1 =>
        rw [hb] at h
        have hRest : Pool.applyRun verify t1 cs = some t := h
        obtain ⟨s1, hStep, hContract⟩ := Pool.apply_backward_refinement verify hReal hTS hOS s hb
        have hReach1 : Pool.machine.Reachable s1 :=
          Pool.machine_reachable_iff.mpr ((Pool.machine_reachable_iff.mp s.reachable).step hStep)
        rw [← hContract] at hRest
        exact Pool.applyRun_reaches_contract verify hReal hTS hOS cs ⟨s1, hReach1⟩ hRest

/-- **Run refinement** (rule PE7): every list of calls that
`Pool.apply verify` accepts in order from the genesis contract reaches the contract of some
reachable state.

For every list of calls, when `Pool.apply verify` accepts them one after another starting from
`(genesis r feeAdmin treasury).contract`, the state the run leaves is `s.contract` for some
reachable `s`, under the same hypothesis as PE5: every public input `verify` accepts has a
witness that satisfies the circuit. Proved by induction on the list
(`Pool.applyRun_reaches_contract`), applying `Pool.apply_backward_refinement` at each call; the
base case is `genesis`'s own reachability (`Reachable.genesis`).

Source: docs/pool-executable.md rule PE7 (design decision 2026-11-09). -/
theorem Pool.apply_backward_refinement_run (verify : Pool.Verifier) (hReal : verify.Realizes)
    (hTS : TransactProofSoundness) (hOS : OwnedProofSoundness)
    (r : FeeRatio) (feeAdmin treasury : Term) (cs : List Pool.Call) {t : Pool.ContractState}
    (h : Pool.applyRun verify (genesis r feeAdmin treasury).contract cs = some t) :
    ∃ s : PoolState, Reachable s ∧ s.contract = t :=
  Pool.applyRun_reaches_contract verify hReal hTS hOS cs
    ⟨genesis r feeAdmin treasury, Pool.machine_reachable_iff.mpr (Reachable.genesis r feeAdmin treasury)⟩
    h

end ArmadaLean
