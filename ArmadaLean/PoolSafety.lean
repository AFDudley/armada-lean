/-
  ArmadaLean.PoolSafety — the pool contract's safety theorems, over ArmadaLean.Pool.
-/
import ArmadaLean.Pool

/-! ### The core invariant: tokens held equal the value of unspent notes -/

/-- The core invariant: for each token, the tokens the pool holds equal the total value
    of its unspent notes, summed over live leaf positions. -/
def HeldInvariant (s : PoolState) : Prop :=
  ∀ t, s.held t = listSum ((s.live t).map (fun p => p.2.value))

theorem genesis_invariant (r : FeeRatio) : HeldInvariant (genesis r) := by
  intro t
  simp [genesis, listSum]

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
      simp [listSum]
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
`transact`/`transactOwned`, and direct construction for `shield`. -/
theorem core_invariant {s : PoolState} (h : Reachable s) :
    HeldInvariant s := by
  induction h with
  | genesis r => exact genesis_invariant r
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
path. -/
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
    · rw [if_pos hmem] at h; exact absurd h (by simp)
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
    · rw [if_pos hmem] at h; exact absurd h (by simp)
    · rw [if_neg hmem] at h
      intro m hm
      rcases ih h m hm with hcase | hcase
      · rcases List.eq_or_mem_of_mem_cons hcase with heq | hcase2
        · exact Or.inr (heq ▸ List.mem_cons_self)
        · exact Or.inl hcase2
      · exact Or.inr (List.mem_cons_of_mem n hcase)

/-- One step never un-spends a nullifier, in any one tree. `spent` is now per-tree
    (`PrivacyPoolStorage.nullifiers`, `treeNumber -> nullifier -> isSpent`,
    PrivacyPoolStorage.sol:174): a step only ever updates tree `treeNumber`'s own
    nullifier set, so for any other tree `s'.spent tn = s.spent tn` trivially, and for
    `tn = treeNumber`, `markSpent_subset` closes it. -/
theorem spent_monotone {s s' : PoolState} (hstep : Step s s') (tn : Nat) :
    ∀ n ∈ s.spent tn, n ∈ s'.spent tn := by
  cases hstep with
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
TransactModule.sol:379-386). S-RG, "RAILGUN Core System & Protocol": "The contract
checks to make sure: ... That it hasn't seen the nullifiers before, eliminating any
double spends." -/
theorem pool_no_double_spend {s0 s : PoolState}
    (_h0 : Reachable s0) (hfrom : ReachableFrom s0 s) (tn : Nat)
    {n : Term} (hn0 : n ∈ s0.spent tn) {ns : List Term} {spent' : NullifierSet}
    (hmark : markSpent (s.spent tn) ns = some spent') : n ∉ ns := by
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
other live position could ever produce that same nullifier under the same key. -/
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
  ⟨removeAll_perm hRemove, by simp⟩

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
    records openings hRoot hRemove hNullify hRecords, by simp [hU], by simp [hU, withdrawn], ?_⟩
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
    insertStart s.trees 1, ?_, ?_, by simp, by simp, by simp, fee_conservation s.feeRatio x,
    fun t ht => ⟨by simp [ht], by simp [ht], by simp [ht]⟩⟩
  · simp [PoolState.leavesAt', insertStart_eq]
  · show (leavesAt (insertLeaves s.trees [_]) (insertTree s.trees 1))[insertStart s.trees 1]? = _
    rw [insertLeaves_leavesAt, if_pos (by rfl), insertStart_eq]
    simp

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
  | genesis r => exact ⟨[], rfl⟩
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
theorem transact_root_was_produced {s : PoolState}
    (h : Reachable s) (tn : Nat) {root : Term} (hRoot : root ∈ s.rootsAt' tn) :
    root ∈ rootsAt genesisTrees tn ∨
      ∃ pushed : List Term, root ∈ pushed ∧ s.rootsAt' tn = pushed ++ rootsAt genesisTrees tn := by
  obtain ⟨pushed, hpushed⟩ := rootsAt_grounded h tn
  rw [hpushed] at hRoot
  rcases List.mem_append.mp hRoot with h1 | h2
  · exact Or.inr ⟨pushed, h1, hpushed⟩
  · exact Or.inl h2

/-! ### The preimage registry -/

/--
**The preimage registry is always consistent.** Every entry the pool has ever written to
`preimageOf`, at any reachable state, hashes to the commitment it is recorded under —
lifting `ArmadaLean.PoolOwned.preimageOf_consistent` from one transaction's batch
(`recordPreimages`) to the pool's whole history (`applyRecords`, at every
`shield`/`transact`/`transactOwned` step). -/
theorem pool_preimageOf_consistent {s : PoolState}
    (h : Reachable s) : RegistryConsistent s.preimageOf := by
  induction h with
  | genesis r => intro c pre hc; simp [genesis] at hc
  | step _ hstep ih =>
    cases hstep with
    | shield token x npk hValue hSpendable =>
      exact recordStep_preserves_consistency ih rfl
    | transact caller w pub bp hN hM hC hBound hAdapt newNotes hOutputs rest spent' records
        openings hRoot hRemove hNullify hRecords =>
      exact applyRecords_preserves_consistency ih
        (fun cp hcp => transactOutputRecords_valid hC cp (hRecords.subset hcp))
    | transactOwned w pub bp hN hM hC caller hCaller hBound hAdapt hNoUnshield rest spent'
        openings hRoot hRemove hNullify =>
      exact applyRecords_preserves_consistency ih (ownedOutputRecords_valid hC)

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
theorem ofFn_pairwise_ne {N : Nat} (f : Fin N → Nat)
    (h : (List.ofFn f).Pairwise (· ≠ ·)) : ∀ i j : Fin N, i ≠ j → f i ≠ f j := by
  rw [List.pairwise_iff_getElem] at h
  intro i j hij
  rcases Nat.lt_or_gt_of_ne (fun heq => hij (Fin.ext heq)) with hlt | hlt
  · have hh := h i.1 j.1 (by simp) (by simp) hlt
    simp only [List.getElem_ofFn] at hh
    simpa using hh
  · have hh := h j.1 i.1 (by simp) (by simp) hlt
    simp only [List.getElem_ofFn] at hh
    intro heq
    exact hh (by simpa using heq.symm)

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
`owned_spend_can_happen` does). -/
theorem transact_spend_can_happen {N M : Nat} (hComplete : TransactProofCompleteness)
    (hSig : HonestSignature) (publicKey : Nat × Nat)
    (nullifyingKey : Nat) (token : Token) (boundParamsHash : Term) (root : Term)
    (randomIn valueIn : Fin N → Nat) (leavesIndices : Fin N → Nat)
    (pathElements : Fin N → List (Term × Bool)) (npkOut : Fin M → Term) (valueOut : Fin M → Nat)
    (hPathLen : ∀ i, (pathElements i).length = 16)
    (hMerkle : ∀ i,
      merkleRoot
        (commitment (npk (masterPublicKey publicKey nullifyingKey) (randomIn i)) token
          (valueIn i))
        (pathElements i) = root)
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
    { pathLen := hPathLen, merkle := hMerkle, nullifiers := fun _ => rfl,
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
theorem shield_can_happen {s : PoolState} (token : Token) (x : Nat) (npk : Term)
    (hValue : 0 < x) (hSpendable : Spendable (shieldBase s.feeRatio x)) :
    ∃ s', Step s s' :=
  ⟨_, Step.shield token x npk hValue hSpendable⟩

/-- **Can happen: a transact (private transfer, no unshield) succeeds.** A real key
    holder with `N` live notes in tree `bp.treeNumber`, re-minting them into `M` new
    notes of equal total value, clears every check of `Step.transact`: the witness is
    built and shown `Constrained` as `transact_spend_can_happen` builds one,
    `hComplete.complete` shows `verify` accepts, and `markSpent_succeeds` (with
    `distinct_leaves_distinct_nullifiers`) shows the nullifiers are fresh. `bp` is the
    transaction's bound parameters, with no unshield (`hNoUnshield`) and an adapt
    contract, if any, equal to `caller` (`hAdapt`). `hLive` is the ghost liveness
    precondition, keyed by the `(treeNumber, leaf position)` pairs of the notes. -/
theorem transact_can_happen {s : PoolState} (hComplete : TransactProofCompleteness)
    (hSig : HonestSignature) {N M : Nat} (caller : Term) (bp : BoundParams)
    (hAdapt : AdaptAllows bp caller) (hNoUnshield : bp.unshield = none)
    (publicKey : Nat × Nat) (nullifyingKey : Nat) (token : Token) (root : Term)
    (randomIn valueIn : Fin N → Nat) (leavesIndices : Fin N → Nat)
    (pathElements : Fin N → List (Term × Bool)) (npkOut : Fin M → Term) (valueOut : Fin M → Nat)
    (hN : N ≤ 8) (hM : M ≤ 4)
    (hRoot : root ∈ s.rootsAt' bp.treeNumber)
    (hPathLen : ∀ i, (pathElements i).length = 16)
    (hMerkle : ∀ i,
      merkleRoot
        (commitment (npk (masterPublicKey publicKey nullifyingKey) (randomIn i)) token
          (valueIn i))
        (pathElements i) = root)
    (hRangeIn : ∀ i, RangeChecked120 (valueIn i))
    (hRangeOut : ∀ j, RangeChecked120 (valueOut j))
    (hBalance : listSum (List.ofFn valueIn) = listSum (List.ofFn valueOut))
    (hDistinctLeaves : (List.ofFn leavesIndices).Pairwise (· ≠ ·))
    (hFresh : ∀ i, nullifier (Term.val nullifyingKey) (leavesIndices i) ∉ s.spent bp.treeNumber)
    {rest : List ((Nat × Nat) × CommitmentPreimage)}
    (hLive : removeAll (s.live token)
        (List.ofFn fun i =>
          ((bp.treeNumber, leavesIndices i),
            (⟨npk (masterPublicKey publicKey nullifyingKey) (randomIn i), token, valueIn i⟩ :
              CommitmentPreimage)))
        = some rest) :
    ∃ s', Step s s' := by
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
    { pathLen := hPathLen, merkle := hMerkle, nullifiers := fun _ => rfl,
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
theorem unshield_can_happen {s : PoolState} (hComplete : TransactProofCompleteness)
    (hSig : HonestSignature) {N : Nat} (caller : Term) (bp : BoundParams)
    (hAdapt : AdaptAllows bp caller) (recipient : Term) (value : Nat)
    (hU : bp.unshield = some ⟨recipient, value⟩)
    (publicKey : Nat × Nat) (nullifyingKey : Nat) (token : Token) (root : Term)
    (randomIn valueIn : Fin N → Nat) (leavesIndices : Fin N → Nat)
    (pathElements : Fin N → List (Term × Bool))
    (hN : N ≤ 8)
    (hRoot : root ∈ s.rootsAt' bp.treeNumber)
    (hPathLen : ∀ i, (pathElements i).length = 16)
    (hMerkle : ∀ i,
      merkleRoot
        (commitment (npk (masterPublicKey publicKey nullifyingKey) (randomIn i)) token
          (valueIn i))
        (pathElements i) = root)
    (hRangeIn : ∀ i, RangeChecked120 (valueIn i)) (hRangeOut : RangeChecked120 value)
    (hBalance : listSum (List.ofFn valueIn) = value)
    (hDistinctLeaves : (List.ofFn leavesIndices).Pairwise (· ≠ ·))
    (hFresh : ∀ i, nullifier (Term.val nullifyingKey) (leavesIndices i) ∉ s.spent bp.treeNumber)
    {rest : List ((Nat × Nat) × CommitmentPreimage)}
    (hLive : removeAll (s.live token)
        (List.ofFn fun i =>
          ((bp.treeNumber, leavesIndices i),
            (⟨npk (masterPublicKey publicKey nullifyingKey) (randomIn i), token, valueIn i⟩ :
              CommitmentPreimage)))
        = some rest) :
    ∃ s', Step s s' ∧ s'.payouts = s.payouts ++ [⟨token, recipient, value⟩] := by
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
    simp [List.ofFn_succ, List.ofFn_zero, listSum, hBalance]
  have hConstrained : Constrained w pub :=
    { pathLen := hPathLen, merkle := hMerkle, nullifiers := fun _ => rfl,
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
    simp [transactAllOutputs, List.ofFn_succ, List.ofFn_zero, w]
  refine ⟨_, Step.transact caller w pub bp hN (by decide) hConstrained rfl hAdapt
    [] hUnshieldRefines rest spent' (transactOutputRecords w pub) []
    hRoot hLive hNullify (List.Sublist.refl _), ?_⟩
  simp [hU, w]

/-- **Can happen: an owned transact succeeds.** Wires an owned witness, built as
    `ArmadaLean.PoolOwned.owned_spend_can_happen` builds one, into
    `Step.transactOwned`: `hLive` is the ghost liveness precondition, `hN`/`hM` the
    registered-shape bound, `caller`/`hCaller` the authorization check
    (`transactOwned_spends_only_owned` is the matching safety theorem), and `bp` the
    bound parameters (no unshield, adapt contract `caller` or none). An owned transact
    can pay out to any recipient's note key; the step publishes no opening
    (`openings := []`). -/
theorem owned_transact_can_happen {s : PoolState} (hComplete : OwnedProofCompleteness)
    {N M : Nat} (ownerField : Term) (token : Token) (bp : BoundParams)
    (hNoUnshield : bp.unshield = none) (root : Term)
    (randomIn valueIn : Fin N → Nat) (leavesIndices : Fin N → Nat)
    (pathElements : Fin N → List (Term × Bool)) (npkOut : Fin M → Term) (valueOut : Fin M → Nat)
    (hN : N ≤ 8) (hM : M ≤ 4)
    (hRoot : root ∈ s.rootsAt' bp.treeNumber)
    (hPathLen : ∀ i, (pathElements i).length = 16)
    (hMerkle : ∀ i,
      merkleRoot (commitment (npk ownerField (randomIn i)) token (valueIn i))
        (pathElements i) = root)
    (hRangeIn : ∀ i, RangeChecked120 (valueIn i))
    (hRangeOut : ∀ j, RangeChecked120 (valueOut j))
    (hBalance : listSum (List.ofFn valueIn) = listSum (List.ofFn valueOut))
    (hDistinctLeaves : (List.ofFn leavesIndices).Pairwise (· ≠ ·))
    (hFresh : ∀ i, nullifier ownerField (leavesIndices i) ∉ s.spent bp.treeNumber)
    (caller : Term) (hCaller : caller = ownerField) (hAdapt : AdaptAllows bp caller)
    {rest : List ((Nat × Nat) × CommitmentPreimage)}
    (hLive : removeAll (s.live token)
        (List.ofFn fun i =>
          ((bp.treeNumber, leavesIndices i),
            (⟨npk ownerField (randomIn i), token, valueIn i⟩ : CommitmentPreimage)))
        = some rest) :
    ∃ s', Step s s' := by
  let pub : TransactOwnedPublic N M :=
    { merkleRoot := root, boundParamsHash := hashBoundParams bp,
      nullifiers := fun i => nullifier ownerField (leavesIndices i),
      commitmentsOut := fun j => commitment (npkOut j) token (valueOut j),
      ownerField := ownerField }
  let w : TransactOwnedWitness N M :=
    { token := token, randomIn := randomIn, valueIn := valueIn, pathElements := pathElements,
      leavesIndices := leavesIndices, npkOut := npkOut, valueOut := valueOut }
  have hConstrained : OwnedConstrained w pub :=
    { pathLen := hPathLen, merkle := hMerkle, nullifiers := fun _ => rfl,
      outputs := fun _ => rfl, rangeIn := hRangeIn, rangeOut := hRangeOut,
      balance := congrArg (· % p) hBalance }
  obtain ⟨spent', hNullify⟩ :
      ∃ spent', markSpent (s.spent bp.treeNumber) (List.ofFn pub.nullifiers) = some spent' := by
    apply markSpent_succeeds
    · have hmap := distinct_leaves_distinct_nullifiers ownerField
        (List.ofFn leavesIndices) hDistinctLeaves
      have heq : (List.ofFn leavesIndices).map (nullifier ownerField)
          = List.ofFn pub.nullifiers := List.map_ofFn
      rwa [heq] at hmap
    · intro n hn
      obtain ⟨i, hi⟩ := List.mem_ofFn.mp hn
      rw [← hi]
      exact hFresh i
  exact ⟨_, Step.transactOwned w pub bp hN hM hConstrained caller hCaller rfl hAdapt
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
  | genesis r =>
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
  | shield token x npk hValue hSpendable =>
    exact insertLeaves_leavesAt_capacity s.trees
      [hashCommitment (⟨npk, token, shieldBase s.feeRatio x⟩ : CommitmentPreimage)] tn
      (by simp; unfold TreeDepth; omega) hOldCap
  | transact caller w pub bp hN hM hC hBound hAdapt newNotes hOutputs rest spent' records
      openings hRoot hRemove hNullify hRecords =>
    have hlen : newNotes.length ≤ 4 := Nat.le_trans (unshieldRefines_length_le hOutputs) hM
    exact insertLeaves_leavesAt_capacity s.trees
      (newNotes.map hashCommitment) tn (by simp; unfold TreeDepth; omega) hOldCap
  | transactOwned w pub bp hN hM hC caller hCaller hBound hAdapt hNoUnshield rest spent'
      openings hRoot hRemove hNullify =>
    have hlen : (ownedNewNotes w).length ≤ 4 := by
      unfold ownedNewNotes
      simp only [List.length_ofFn]
      omega
    exact insertLeaves_leavesAt_capacity s.trees
      ((ownedNewNotes w).map hashCommitment) tn (by simp; unfold TreeDepth; omega) hOldCap

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
  | genesis r =>
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
theorem leaf_has_merkle_witness {s : PoolState} (h : Reachable s) (tn : Nat)
    {i : Nat} {leaf : Term} (hleaf : (s.leavesAt' tn)[i]? = some leaf) :
    merkleRoot leaf (treePath TreeDepth (s.leavesAt' tn) i) =
        treeRoot TreeDepth (s.leavesAt' tn) ∧
      treeRoot TreeDepth (s.leavesAt' tn) ∈ s.rootsAt' tn := by
  obtain ⟨hi, _⟩ := List.getElem?_eq_some_iff.mp hleaf
  have hcap := reachable_leavesAt_capacity h tn
  have hilt : i < 2 ^ TreeDepth := Nat.lt_of_lt_of_le hi hcap
  refine ⟨treePath_correct_of_getElem? TreeDepth (s.leavesAt' tn) i hilt hleaf, ?_⟩
  rcases reachable_rootAt_matches_leavesAt h tn with hnil | hmem
  · rw [hnil] at hleaf; simp at hleaf
  · exact hmem

/-! ### A leaf, once inserted, never moves

The pool's Merkle tree is append-only. `MerkleModule` is an "Append-only incremental
binary Merkle tree over Poseidon" (MerkleModule.sol:12). `insertLeaves`
(MerkleModule.sol:54-121) writes new leaves at `nextLeafIndex` and later positions only,
and no function removes or rewrites a leaf. The Railgun whitepaper (S-RG, "RAILGUN
Core System & Protocol"; armada-laconic `.scratch/rewrite-B/railgun-whitepaper-2021.txt`
:161-163 and :234-235) keeps the notes in "batch incremental Merkle trees", and "The
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
openings `(ownerField, r)` appear in a list of published openings (`hOwned`; callers
instantiate `published := s.published`, decision 11) and match the note's `npk`, a
satisfying `OwnedConstrained` witness/public pair exists. Its Merkle path is
`treePath TreeDepth leaves`, computed, not chosen. The pool does not check a published
opening; `hOwned` is the reader's own check against `npk`. -/
theorem owned_spend_witness_exists {N M : Nat}
    (ownerField : Term) (token : Token) (boundParamsHash : Term)
    (preimages : Fin N → CommitmentPreimage)
    (leavesIndices : Fin N → Nat) (leaves : List Term)
    (published : List (Term × OwnedOpening))
    (hToken : ∀ i, (preimages i).token = token)
    (hOwned : ∀ i, ∃ r, (hashCommitment (preimages i), ⟨ownerField, r⟩) ∈ published ∧
      npk ownerField r = (preimages i).npk)
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
      pub.ownerField = ownerField ∧
      w.token = token ∧
      (∀ i, w.valueIn i = (preimages i).value) := by
  let r : Fin N → Nat := fun i => (hOwned i).choose
  let pub : TransactOwnedPublic N M :=
    { merkleRoot := treeRoot TreeDepth leaves, boundParamsHash := boundParamsHash,
      nullifiers := fun i => nullifier ownerField (leavesIndices i),
      commitmentsOut := fun j => commitment (npkOut j) token (valueOut j),
      ownerField := ownerField }
  let w : TransactOwnedWitness N M :=
    { token := token, randomIn := r,
      valueIn := fun i => (preimages i).value,
      pathElements := fun i => treePath TreeDepth leaves (leavesIndices i),
      leavesIndices := leavesIndices, npkOut := npkOut, valueOut := valueOut }
  have hConstrained : OwnedConstrained w pub :=
    { pathLen := fun i => treePath_length TreeDepth leaves (leavesIndices i),
      merkle := fun i => by
        have hr := (hOwned i).choose_spec
        have hge : leaves[leavesIndices i]? =
            some (commitment (npk ownerField (r i)) token ((preimages i).value)) := by
          rw [hr.2, ← hToken i]
          exact hLeafValue i
        exact treePath_correct_of_getElem? TreeDepth leaves (leavesIndices i) (hLeafIndex i) hge,
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

theorem genesis_live_spent_invariant (r : FeeRatio) : LiveSpentInvariant (genesis r) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> intro <;> simp [genesis]

theorem step_preserves_live_spent_invariant {s s' : PoolState} (ih : LiveSpentInvariant s)
    (hstep : Step s s') : LiveSpentInvariant s' := by
  obtain ⟨ih1, ih2, ih3, ih4, ih5⟩ := ih
  simp only [PoolState.leavesAt'] at ih1 ih3
  cases hstep with
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
  | genesis r => exact genesis_live_spent_invariant r
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
theorem live_note_unspent {s : PoolState} (h : Reachable s) (t : Token) (tn pos : Nat)
    (pre : CommitmentPreimage) (hmem : ((tn, pos), pre) ∈ s.live t) (nk : Term) :
    nullifier nk pos ∉ s.spent tn :=
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
    have hlenEq : (newNotes.map hashCommitment).length = newNotes.length := by simp
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
    have hlenEq : ((ownedNewNotes w).map hashCommitment).length = (ownedNewNotes w).length := by simp
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
  | genesis r => intro t tn pos pre hmem; simp [genesis] at hmem
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
theorem live_leaf_matches {s : PoolState} (h : Reachable s) (t : Token) (tn pos : Nat)
    (pre : CommitmentPreimage) (hmem : ((tn, pos), pre) ∈ s.live t) :
    (s.leavesAt' tn)[pos]? = some (hashCommitment pre) := by
  have hmatch := reachable_live_leaf_matches h t tn pos pre hmem
  have hrange := (reachable_live_spent_invariant h).1 t tn pos pre hmem
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hrange] at hmatch
  rw [List.getElem?_eq_getElem hrange]
  exact congrArg some hmatch

/-! ### Every live note is spendable -/

/-- Every live note's value passes the circuit's input range check (`Spendable`,
    `ArmadaLean.RangeCheck`). -/
def LiveValuesSpendable (s : PoolState) : Prop :=
  ∀ t p, p ∈ s.live t → Spendable p.2.value

theorem genesis_live_values_spendable (r : FeeRatio) :
    LiveValuesSpendable (genesis r) := by
  intro t p hp
  simp [genesis] at hp

theorem step_preserves_live_values_spendable {s s' : PoolState} (ih : LiveValuesSpendable s)
    (hstep : Step s s') : LiveValuesSpendable s' := by
  cases hstep with
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
theorem live_values_spendable {s : PoolState} (h : Reachable s) :
    LiveValuesSpendable s := by
  induction h with
  | genesis r => exact genesis_live_values_spendable r
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
theorem spend_not_blocked {s s' : PoolState} (hs : Reachable s) (hstep : Step s s')
    {tn : Nat} {root nk : Term} {token : Token}
    {entries : List ((Nat × Nat) × CommitmentPreimage)}
    (hTree : ∀ e ∈ entries, e.1.1 = tn)
    (hEnabled : SpendEnabled s tn root token entries (entries.map fun e => nullifier nk e.1.2))
    (hDisjoint : ∀ e ∈ entries, ¬ Spends s s' token e) :
    SpendEnabled s' tn root token entries (entries.map fun e => nullifier nk e.1.2) := by
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
    any step that spends none of its input notes. -/
theorem transact_not_blocked {s s' : PoolState} (hs : Reachable s) (hstep : Step s s')
    {N M : Nat} {w : TransactWitness N M} {pub : TransactPublic N M} {bp : BoundParams}
    (hC : Constrained w pub)
    (hEnabled : SpendEnabled s bp.treeNumber pub.merkleRoot w.token
      (transactSpentPositions bp.treeNumber w) (List.ofFn pub.nullifiers))
    (hDisjoint : ∀ e ∈ transactSpentPositions bp.treeNumber w, ¬ Spends s s' w.token e) :
    SpendEnabled s' bp.treeNumber pub.merkleRoot w.token
      (transactSpentPositions bp.treeNumber w) (List.ofFn pub.nullifiers) := by
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
  exact spend_not_blocked hs hstep hTree hEnabled hDisjoint

/-- `spend_not_blocked` for a pending `Step.transactOwned`: its state checks stay true
    across any step that spends none of its input notes. -/
theorem transactOwned_not_blocked {s s' : PoolState} (hs : Reachable s) (hstep : Step s s')
    {N M : Nat} {w : TransactOwnedWitness N M} {pub : TransactOwnedPublic N M}
    {bp : BoundParams} (hC : OwnedConstrained w pub)
    (hEnabled : SpendEnabled s bp.treeNumber pub.merkleRoot w.token
      (ownedSpentPositions bp.treeNumber pub w) (List.ofFn pub.nullifiers))
    (hDisjoint : ∀ e ∈ ownedSpentPositions bp.treeNumber pub w, ¬ Spends s s' w.token e) :
    SpendEnabled s' bp.treeNumber pub.merkleRoot w.token
      (ownedSpentPositions bp.treeNumber pub w) (List.ofFn pub.nullifiers) := by
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
  exact spend_not_blocked hs hstep hTree hEnabled hDisjoint

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

/-! ### An owned merge (theorem 3 of the channel design) -/

/--
**Can happen: an owned transact merges several notes of one owner into one note.** In a
reachable state, take `N` (`1 ≤ N ≤ 8`) live notes of `token` at distinct positions of
tree `bp.treeNumber`, all owned by `owner` (`hOpen`: each note's `npk` is
`npk owner (random i)`). If the sum of their values passes the circuit's range check
(`hSum`), the owner can spend all of them in one `Step.transactOwned` with one output
of exactly that sum, to the note key `npkOut`. After the step none of the inputs is
live, the output is live, and the pool's custody of `token` is unchanged: value is
conserved. The witness comes from public data (`owned_spend_witness_exists`,
`live_leaf_matches`, `live_note_unspent`, `live_values_spendable`).

The deployed owned circuits have one input only (`main_{1x1,1x2,1x3}_owned.circom`).
The model's owned path admits `N ≤ 8`, so this theorem needs owned verifying keys with
`N > 1` at deployment. -/
theorem owned_merge_can_happen {s : PoolState} (hs : Reachable s) {N : Nat}
    (hN0 : 0 < N) (hN : N ≤ 8)
    (owner : Term) (token : Token) (bp : BoundParams)
    (hNoUnshield : bp.unshield = none) (hAdapt : AdaptAllows bp owner)
    (pos : Fin N → Nat) (pre : Fin N → CommitmentPreimage) (random : Fin N → Nat)
    (hLive : ∀ i, ((bp.treeNumber, pos i), pre i) ∈ s.live token)
    (hDistinct : (List.ofFn pos).Pairwise (· ≠ ·))
    (hOpen : ∀ i, npk owner (random i) = (pre i).npk)
    (npkOut : Term)
    (hSum : Spendable (listSum (List.ofFn fun i => (pre i).value))) :
    ∃ s', Step s s' ∧
      (∀ i, ((bp.treeNumber, pos i), pre i) ∉ s'.live token) ∧
      (∃ tn' pos' : Nat, ((tn', pos'),
        (⟨npkOut, token, listSum (List.ofFn fun i => (pre i).value)⟩ : CommitmentPreimage))
          ∈ s'.live token) ∧
      s'.held token = s.held token := by
  sorry
