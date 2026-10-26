/-
  ArmadaLean.PoolSafety — the pool contract's safety theorems, over ArmadaLean.Pool.
-/
import ArmadaLean.Pool

/-! ### The core invariant: tokens held equal the value of unspent notes -/

/-- The core invariant: for each token, the tokens the pool holds equal the total value
    of its unspent notes, summed over live leaf positions. -/
def HeldInvariant (s : PoolState) : Prop :=
  ∀ t, s.held t = listSum ((s.live t).map (fun p => p.2.value))

theorem genesis_invariant : HeldInvariant genesis := by
  intro t
  simp [genesis, listSum]

/-- The value projection of a `List.ofFn`-built list of notes, all sharing one `token`
    and one key-derivation `mk`, is exactly the underlying value function. Bridges the
    circuit's `Fin`-indexed `valueIn`/`valueOut` and the pool's `List`-indexed note
    bookkeeping everywhere below. `mk` produces note public keys, hence `Term`. -/
theorem value_ofFn_eq {N : Nat} (mk : Fin N → Term) (g : Fin N → Nat) (token : Nat) :
    (List.ofFn (fun i => (⟨mk i, token, g i⟩ : CommitmentPreimage))).map
        CommitmentPreimage.value = List.ofFn g := by
  rw [List.map_ofFn]
  rfl

/-- The position-tagged counterpart of `value_ofFn_eq`: tagging each note with a
    position (`transactSpentPositions`/`ownedSpentPositions`'s own shape, now
    `(treeNumber, leafIndex)` pairs) does not touch the value projection. Polymorphic
    in the tag type `β`, since the tag is now a pair, not a bare `Nat`. -/
theorem value_ofFn_pos_eq {N : Nat} {β : Type} (pos : Fin N → β) (mk : Fin N → Term)
    (g : Fin N → Nat) (token : Nat) :
    (List.ofFn (fun i => (pos i, (⟨mk i, token, g i⟩ : CommitmentPreimage)))).map
        (fun p => p.2.value) = List.ofFn g := by
  rw [List.map_ofFn]
  rfl

/-- **The balance a `Step.transact` moves is derived, not assumed.** `transactSpentPositions`
    and `transactAllOutputs` are built straight from the witness; `transact_value_conserved`
    (`ArmadaLean.Transact`) — which needs exactly the registered-shape bound `hN`/`hM` to
    upgrade the circuit's mod-`p` equality to an integer one — gives their values' sum
    equality, and `hSplit` carries that equality across the split into kept notes and the
    unshield payout. This is the fact `Step.transact`'s own comment points to instead of
    taking it as a hypothesis. -/
theorem transact_balance {N M : Nat} {w : TransactWitness N M} {pub : TransactPublic N M}
    (treeNumber : Nat) (hN : N ≤ 8) (hM : M ≤ 4) (hC : Constrained w pub)
    {newNotes unshieldTail : List CommitmentPreimage}
    (hSplit : transactAllOutputs w = newNotes ++ unshieldTail) :
    listSum ((transactSpentPositions treeNumber w).map (fun p => p.2.value)) =
      listSum (newNotes.map CommitmentPreimage.value) +
        listSum (unshieldTail.map CommitmentPreimage.value) := by
  have hbal := transact_value_conserved w pub hN hM hC
  have hSplit' := congrArg (List.map CommitmentPreimage.value) hSplit
  rw [List.map_append] at hSplit'
  unfold transactAllOutputs at hSplit'
  rw [value_ofFn_eq] at hSplit'
  unfold transactSpentPositions
  rw [value_ofFn_pos_eq, hbal, hSplit', listSum_append]

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
  | shield token grossAmount feeBP npk hNotPaused hValue hFeeBP hRange =>
    intro t
    by_cases ht : t = token
    · simp only [ht, if_pos]
      have hinv_t := hinv token
      simp only [List.map_cons, listSum]
      omega
    · simp only [if_neg ht]
      exact hinv t
  | transact w pub treeNumber hN hM hC newNotes unshieldTail rest spent' records ownedRecords
      hRoot hSplit hUnshieldLen hRemove hNullify hRecords hOwnedRecords =>
    intro t
    by_cases ht : t = w.token
    · subst ht
      simp only [if_pos]
      have hsum := removeAll_sum (fun p => p.2.value) hRemove
      have hbal := transact_balance treeNumber hN hM hC hSplit
      have hinv_t := hinv w.token
      have hpos := withTreePositionsFrom_map CommitmentPreimage.value
        (insertTreeNumber s.closedTrees s.leaves newNotes.length)
        (insertStartPos s.leaves newNotes.length) newNotes
      simp only [List.map_append, listSum_append]
      rw [hpos]
      omega
    · simp only [if_neg ht]
      exact hinv t
  | transactOwned w pub treeNumber hN hM hC caller hCaller rest spent' ownedOutputs
      hRoot hRemove hNullify hNonZero hOwnedOutputs =>
    intro t
    by_cases ht : t = w.token
    · subst ht
      simp only [if_pos]
      have hsum := removeAll_sum (fun p => p.2.value) hRemove
      have hbal := transactOwned_balance treeNumber hN hM hC
      have hinv_t := hinv w.token
      have hpos := withTreePositionsFrom_map CommitmentPreimage.value
        (insertTreeNumber s.closedTrees s.leaves (ownedNewNotes w).length)
        (insertStartPos s.leaves (ownedNewNotes w).length) (ownedNewNotes w)
      simp only [List.map_append, listSum_append]
      rw [hpos]
      omega
    · simp only [if_neg ht]
      exact hinv t
  | admin shieldsPaused =>
    intro t
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
  | genesis => exact genesis_invariant
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

/-! ### No step can block an otherwise-valid spend -/

/--
**No step any caller can take, the owner included, can make a `transact` that is
otherwise valid fail.** `Step.transact`'s only preconditions on the source state `s`
are `hRoot : pub.merkleRoot ∈ s.rootsAt' treeNumber`, `hRemove : removeAll (s.live
w.token) (transactSpentPositions treeNumber w) = some rest` and `hNullify : markSpent
(s.spent treeNumber) (...) = some spent'`. None of them reads `s.shieldsPaused`, the
one field any step other than `Step.shield`/`.transact`/`.transactOwned` can change
(`Step.admin`, the one remaining owner-controlled path — the module comment on
`Step.transact` records the departure this closes). So the exact witnesses that make a
`transact` valid from `s` also make the identical `transact` valid from `s` with
`shieldsPaused` flipped to any `b`: an admin step can never turn a valid spend into an
invalid one. The proof is immediate reapplication of `Step.transact`'s own
constructor — the state `{ s with shieldsPaused := b }` agrees with `s` on
`closedTrees`/`leaves`/`roots`/`live`/`spent` definitionally, since a record-field
update touches only the one field named. -/
theorem transact_cannot_be_blocked {s : PoolState} (b : Bool)
    {N M : Nat} (w : TransactWitness N M) (pub : TransactPublic N M) (treeNumber : Nat)
    (hN : N ≤ 8) (hM : M ≤ 4) (hC : Constrained w pub)
    (newNotes unshieldTail : List CommitmentPreimage)
    (rest : List ((Nat × Nat) × CommitmentPreimage)) (spent' : NullifierSet)
    (records : List (Term × CommitmentPreimage))
    (ownedRecords : List (Term × OwnedDisclosure))
    (hRoot : pub.merkleRoot ∈ s.rootsAt' treeNumber)
    (hSplit : transactAllOutputs w = newNotes ++ unshieldTail)
    (hUnshieldLen : unshieldTail.length ≤ 1)
    (hRemove : removeAll (s.live w.token) (transactSpentPositions treeNumber w) = some rest)
    (hNullify : markSpent (s.spent treeNumber) (List.ofFn pub.nullifiers) = some spent')
    (hRecords : records.Sublist (transactOutputRecords w pub))
    (hOwnedRecords : ∀ cd ∈ ownedRecords, ∃ pre, (cd.1, pre) ∈ records ∧
      npk cd.2.ownerField cd.2.random = pre.npk) :
    ∃ s', Step { s with shieldsPaused := b } s' :=
  ⟨_, Step.transact w pub treeNumber hN hM hC newNotes unshieldTail rest spent' records
    ownedRecords hRoot hSplit hUnshieldLen hRemove hNullify hRecords hOwnedRecords⟩

/-- The owned-path counterpart of `transact_cannot_be_blocked`: no step any caller can
    take, the owner included, can make an otherwise-valid `transactOwned` fail. Same
    proof shape: `Step.transactOwned`'s preconditions never read `s.shieldsPaused`
    either. -/
theorem transactOwned_cannot_be_blocked {s : PoolState} (b : Bool)
    {N M : Nat} (w : TransactOwnedWitness N M) (pub : TransactOwnedPublic N M)
    (treeNumber : Nat) (hN : N ≤ 8) (hM : M ≤ 4) (hC : OwnedConstrained w pub)
    (caller : Term) (hCaller : caller = pub.ownerField)
    (rest : List ((Nat × Nat) × CommitmentPreimage)) (spent' : NullifierSet)
    (ownedOutputs : List (Fin M × OwnedDisclosure))
    (hRoot : pub.merkleRoot ∈ s.rootsAt' treeNumber)
    (hRemove : removeAll (s.live w.token) (ownedSpentPositions treeNumber pub w) = some rest)
    (hNullify : markSpent (s.spent treeNumber) (List.ofFn pub.nullifiers) = some spent')
    (hNonZero : ∀ j, ¬ isZeroPreimage
      (⟨w.npkOut j, w.token, w.valueOut j⟩ : CommitmentPreimage))
    (hOwnedOutputs : ∀ x ∈ ownedOutputs, npk x.2.ownerField x.2.random = w.npkOut x.1) :
    ∃ s', Step { s with shieldsPaused := b } s' :=
  ⟨_, Step.transactOwned w pub treeNumber hN hM hC caller hCaller rest spent' ownedOutputs
    hRoot hRemove hNullify hNonZero hOwnedOutputs⟩

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
  | shield token grossAmount feeBP npk hNotPaused hValue hFeeBP hRange =>
    exact fun n hn => hn
  | transact w pub treeNumber hN hM hC newNotes unshieldTail rest spent' records ownedRecords
      hRoot hSplit hUnshieldLen hRemove hNullify hRecords hOwnedRecords =>
    by_cases htn : tn = treeNumber
    · subst tn; simp only; exact markSpent_subset hNullify
    · simp only [if_neg htn]; exact fun n hn => hn
  | transactOwned w pub treeNumber hN hM hC caller hCaller rest spent' ownedOutputs
      hRoot hRemove hNullify hNonZero hOwnedOutputs =>
    by_cases htn : tn = treeNumber
    · subst tn; simp only; exact markSpent_subset hNullify
    · simp only [if_neg htn]; exact fun n hn => hn
  | admin shieldsPaused =>
    exact fun n hn => hn

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
theorem spend_live_exact {s : PoolState} {token : Nat}
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
**An unshield sends out exactly the value of the notes it spends minus what stays in
new notes.** `transact_balance` (derived from `transact_value_conserved` at the
registered-shape bound, not assumed) splits the spent notes' value exactly into the new
notes' value and the unshield payout's value; rearranged, the payout is the spent value
minus what the new notes keep. The pool's custody of the token drops by exactly that
amount (`Step.transact`'s `held` field). -/
theorem transact_unshield_exact {spentNotes newNotes unshieldTail : List CommitmentPreimage}
    (hBalance : listSum (spentNotes.map CommitmentPreimage.value) =
        listSum (newNotes.map CommitmentPreimage.value) +
          listSum (unshieldTail.map CommitmentPreimage.value)) :
    listSum (unshieldTail.map CommitmentPreimage.value) =
      listSum (spentNotes.map CommitmentPreimage.value) -
        listSum (newNotes.map CommitmentPreimage.value) := by omega

/--
**A shield creates exactly one note of the shielded amount minus the fee, at the
position `live` reports.** By `Step.shield`'s construction: the live set of the
shielded token gains exactly the one `((treeNumber, position), preimage)` entry
`((insertTreeNumber s.closedTrees s.leaves 1, insertStartPos s.leaves 1), ⟨npk, token,
shieldBase feeBP grossAmount⟩)` — the tree number and position the caller can record as
where its new note sits, whichever tree currently has room (rolling over first if it
does not, module comment on the rollover departure); the pool's custody of that token
rises by exactly that note's value; neither changes for any other token; no second
("fee") note is created (see the module comment on the departure from the brief's
design and from the design labbook). `hRange` replaces the former capacity hypothesis:
a full tree rolls over instead of blocking the shield, so the only remaining gate on
the note's own value is its field width (`live_values_lt_2pow120` lifts this
pool-wide). S-RG, "RAILGUN Core System & Protocol": "Then the smart contract transfers
tokens from the user wallet to itself, if a deposit amount is specified ... The hashes
of the output UTXOs are then added to the Merkle tree." -/
theorem shield_creates_exactly {s : PoolState} (token grossAmount feeBP : Nat) (npk : Term)
    (hNotPaused : s.shieldsPaused = false) (hValue : 0 < grossAmount)
    (hFeeBP : feeBP ≤ BASIS) (hRange : RangeChecked120 (shieldBase feeBP grossAmount)) :
    ∃ s', Step s s' ∧
      s'.live token =
        ((insertTreeNumber s.closedTrees s.leaves 1, insertStartPos s.leaves 1),
          (⟨npk, token, shieldBase feeBP grossAmount⟩ : CommitmentPreimage)) :: s.live token ∧
      s'.held token = s.held token + shieldBase feeBP grossAmount ∧
      (∀ t, t ≠ token → s'.live t = s.live t ∧ s'.held t = s.held t) :=
  ⟨_, Step.shield token grossAmount feeBP npk hNotPaused hValue hFeeBP hRange,
    by simp, by simp, fun t ht => ⟨by simp [ht], by simp [ht]⟩⟩

/-! ### A transact names only a root the pool actually produced -/

/-- One step either leaves tree `tn`'s roots unchanged (`Step.admin`, or any
    `shield`/`transact`/`transactOwned` step that inserted into a *different* tree) or
    prepends exactly one new root to it (`insertResult_rootsAt`, applied to whichever
    batch the constructor inserts) — the structural fact `rootsAt_grounded` needs,
    stated without naming the pushed root's value, since each constructor computes a
    different one. -/
theorem step_rootsAt_shape {s s' : PoolState} (hstep : Step s s') (tn : Nat) :
    s'.rootsAt' tn = s.rootsAt' tn ∨ ∃ r, s'.rootsAt' tn = r :: s.rootsAt' tn := by
  cases hstep with
  | shield token grossAmount feeBP npk hNotPaused hValue hFeeBP hRange =>
    exact insertResult_rootsAt s.closedTrees s.leaves s.roots
      [hashCommitment (⟨npk, token, shieldBase feeBP grossAmount⟩ : CommitmentPreimage)] tn
  | transact w pub treeNumber hN hM hC newNotes unshieldTail rest spent' records ownedRecords
      hRoot hSplit hUnshieldLen hRemove hNullify hRecords hOwnedRecords =>
    exact insertResult_rootsAt s.closedTrees s.leaves s.roots (newNotes.map hashCommitment) tn
  | transactOwned w pub treeNumber hN hM hC caller hCaller rest spent' ownedOutputs
      hRoot hRemove hNullify hNonZero hOwnedOutputs =>
    exact insertResult_rootsAt s.closedTrees s.leaves s.roots
      ((ownedNewNotes w).map hashCommitment) tn
  | admin shieldsPaused =>
    exact Or.inl rfl

/-- Every reachable state's tree-`tn` root history is `genesis.rootsAt' tn` with zero
    or more roots the pool itself pushed to that tree, prepended. -/
theorem rootsAt_grounded {s : PoolState} (h : Reachable s) (tn : Nat) :
    ∃ pushed : List Term, s.rootsAt' tn = pushed ++ genesis.rootsAt' tn := by
  induction h with
  | genesis => exact ⟨[], rfl⟩
  | step _ hstep ih =>
    obtain ⟨pushed, hpushed⟩ := ih
    rcases step_rootsAt_shape hstep tn with heq | ⟨r, heq⟩
    · exact ⟨pushed, heq.trans hpushed⟩
    · exact ⟨r :: pushed, by rw [heq, hpushed, List.cons_append]⟩

/--
**A transact names only a root the pool actually produced, for the tree it names.**
`rootsAt_grounded` shows `s.rootsAt' tn`, for any reachable `s` and tree `tn`, is built
from `genesis.rootsAt' tn` by prepending values the pool itself pushed to that tree at
earlier `shield`/`transact`/`transactOwned` steps — never anything else. A
`transact`/`transactOwned`/`shield` step's own `hRoot : pub.merkleRoot ∈ s.rootsAt'
treeNumber` precondition then means the named root is one of those pushed values, or
the genesis root of that tree — never a caller's invention. S-RG, "RAILGUN Core System
& Protocol": "The contract checks to make sure: ... The Merkle root is the current or a
previous Merkle root, to prevent users from making up UTXOs." -/
theorem transact_root_was_produced {s : PoolState}
    (h : Reachable s) (tn : Nat) {root : Term} (hRoot : root ∈ s.rootsAt' tn) :
    root ∈ genesis.rootsAt' tn ∨
      ∃ pushed : List Term, root ∈ pushed ∧ s.rootsAt' tn = pushed ++ genesis.rootsAt' tn := by
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
  | genesis => intro c pre hc; simp [genesis] at hc
  | step _ hstep ih =>
    cases hstep with
    | shield token grossAmount feeBP npk hNotPaused hValue hFeeBP hRange =>
      exact recordStep_preserves_consistency ih rfl
    | transact w pub treeNumber hN hM hC newNotes unshieldTail rest spent' records ownedRecords
        hRoot hSplit hUnshieldLen hRemove hNullify hRecords hOwnedRecords =>
      exact applyRecords_preserves_consistency ih
        (fun cp hcp => transactOutputRecords_valid hC cp (hRecords.subset hcp))
    | transactOwned w pub treeNumber hN hM hC caller hCaller rest spent' ownedOutputs
        hRoot hRemove hNullify hNonZero hOwnedOutputs =>
      exact applyRecords_preserves_consistency ih (ownedOutputRecords_valid hC)
    | admin shieldsPaused =>
      exact ih

/--
**After an owned transact, the pool's preimage registry returns exactly this output's
own preimage for its own commitment.** `transactOwned` discloses every output, with no
zero preimage among them (`_validatePublicOutputs(requireAll = true)`,
TransactModule.sol:630-634; `Step.transactOwned`'s `hNonZero`), so folding
`ownedOutputRecords w pub` through `applyRecords` never skips one, and
`applyRecords_returns` shows the fold settles exactly there, whatever else the batch
later writes to the same key (never actually different, by `hashCommitment_inj`: two
outputs sharing a commitment must share a preimage). -/
theorem transactOwned_records_all {reg : PreimageRegistry} {N M : Nat}
    {w : TransactOwnedWitness N M} {pub : TransactOwnedPublic N M}
    (hC : OwnedConstrained w pub)
    (hNonZero : ∀ j, ¬ isZeroPreimage (⟨w.npkOut j, w.token, w.valueOut j⟩ : CommitmentPreimage))
    (j : Fin M) :
    applyRecords reg (ownedOutputRecords w pub) (pub.commitmentsOut j) =
      some (⟨w.npkOut j, w.token, w.valueOut j⟩ : CommitmentPreimage) := by
  apply applyRecords_returns (ownedOutputRecords_valid hC)
  · unfold ownedOutputRecords
    exact List.mem_ofFn.mpr ⟨j, rfl⟩
  · exact hNonZero j

/-! ### The owned-random registry is always consistent -/

/--
**The owned-random registry is always consistent against the preimage registry.** Every
entry the pool has ever written to `ownedRandomOf`, at any reachable state, genuinely
reconstructs the matching `preimageOf` entry's `npk` — lifting
`ArmadaLean.PoolOwned.recordOwnedStep_preserves_consistency` to the pool's whole
history. `Step.shield`/`.admin` leave `ownedRandomOf` untouched (`applyRecords
_preserves_other`/`recordStep_preserves_other` show their own `preimageOf` writes
cannot disturb an already-established entry); `Step.transactOwned`'s own
`hOwnedOutputs` check is exactly what `applyOwnedRecords_preserves_consistency` needs
for its optional, per-output disclosure (every output's PREIMAGE stays mandatory,
`transactOwned_records_all`; only the random is optional, since an owned spend can pay
out to a recipient's own note key); `Step.transact`'s `hOwnedRecords` is exactly what
the same lemma needs for its own optional, caller-chosen disclosure, using
`npk_preimage_not_zero` to show the record it points at in `records` was never
skipped by `applyRecords`. -/
theorem pool_ownedRandomOf_consistent {s : PoolState} (h : Reachable s) :
    OwnedRandomConsistent s.preimageOf s.ownedRandomOf := by
  induction h with
  | genesis => intro c d hc; simp [genesis] at hc
  | step hs hstep ih =>
    cases hstep with
    | shield token grossAmount feeBP npk hNotPaused hValue hFeeBP hRange =>
      intro c d hc
      obtain ⟨pre, hreg, hnpk⟩ := ih c d hc
      exact ⟨pre, recordStep_preserves_other (pool_preimageOf_consistent hs c pre hreg) hreg rfl,
        hnpk⟩
    | transact w pub treeNumber hN hM hC newNotes unshieldTail rest spent' records ownedRecords
        hRoot hSplit hUnshieldLen hRemove hNullify hRecords hOwnedRecords =>
      apply applyOwnedRecords_preserves_consistency
      · intro c d hc
        obtain ⟨pre, hreg, hnpk⟩ := ih c d hc
        exact ⟨pre, applyRecords_preserves_other
          (fun cp hcp => transactOutputRecords_valid hC cp (hRecords.subset hcp))
          (pool_preimageOf_consistent hs c pre hreg) hreg, hnpk⟩
      · intro cd hcd
        obtain ⟨pre, hpre, hnpk⟩ := hOwnedRecords cd hcd
        refine ⟨pre, ?_, hnpk⟩
        exact applyRecords_returns (fun cp hcp => transactOutputRecords_valid hC cp (hRecords.subset hcp))
          hpre (npk_preimage_not_zero hnpk)
    | transactOwned w pub treeNumber hN hM hC caller hCaller rest spent' ownedOutputs
        hRoot hRemove hNullify hNonZero hOwnedOutputs =>
      apply applyOwnedRecords_preserves_consistency
      · intro c d hc
        obtain ⟨pre, hreg, hnpk⟩ := ih c d hc
        exact ⟨pre, applyRecords_preserves_other (ownedOutputRecords_valid hC)
          (pool_preimageOf_consistent hs c pre hreg) hreg, hnpk⟩
      · intro cd hcd
        obtain ⟨x, hx, hxeq⟩ := List.mem_map.mp hcd
        obtain ⟨j, d⟩ := x
        refine ⟨⟨w.npkOut j, w.token, w.valueOut j⟩, ?_, ?_⟩
        · rw [← hxeq]
          exact transactOwned_records_all hC hNonZero j
        · rw [← hxeq]
          exact hOwnedOutputs (j, d) hx
    | admin shieldsPaused =>
      exact ih

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
    (nullifyingKey token boundParamsHash : Nat) (root : Term)
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

/-- **Can happen: a shield succeeds.** Any positive amount, at any fee rate up to 100%,
    while shields are not paused, creates a note (`shield_creates_exactly`). No proof, no
    honest-prover assumption: shield carries no SNARK. No capacity gate either: a full
    tree rolls over to a fresh one instead of blocking the shield (`hRange` is the
    note's own `uint120` field width, module comment on the rollover departure). -/
theorem shield_can_happen {s : PoolState} (token grossAmount feeBP : Nat) (npk : Term)
    (hNotPaused : s.shieldsPaused = false) (hValue : 0 < grossAmount)
    (hFeeBP : feeBP ≤ BASIS) (hRange : RangeChecked120 (shieldBase feeBP grossAmount)) :
    ∃ s', Step s s' :=
  ⟨_, Step.shield token grossAmount feeBP npk hNotPaused hValue hFeeBP hRange⟩

/-- **Can happen: a transact (private transfer, no unshield) succeeds.** A real key
    holder with `N` genuinely-held, genuinely-live notes at tree `treeNumber`,
    re-minting them into `M` fresh notes of equal total value, clears every gate
    `Step.transact` checks: the witness is built and shown `Constrained` exactly as
    `transact_spend_can_happen` builds one (inlined here, not obtained from that
    theorem's existential, so `w`'s fields stay definitionally the caller's own
    data — `Step.transact`'s `hRemove`/`hSplit` hypotheses need that transparency),
    `hComplete.complete` shows `verify` accepts, and `markSpent_succeeds` (with
    `distinct_leaves_distinct_nullifiers`) shows the nullifiers are fresh against tree
    `treeNumber`'s own spent set. `hLive` is the ghost liveness precondition, keyed by
    the exact `(treeNumber, leaf position)` pairs the holder's notes sit at (the
    model's own record of what it minted for them earlier, and where); `hN`/`hM` the
    registered-shape bound. No capacity gate: the new outputs land wherever the
    current tree has room, rolling over first if needed. `records := []`,
    `ownedRecords := []`: a plain transact's `publicOutputs` is optional
    (TransactModule.sol:556-561), so no contract-owned output is needed here. -/
theorem transact_can_happen {s : PoolState} (hComplete : TransactProofCompleteness)
    (hSig : HonestSignature) {N M : Nat} (publicKey : Nat × Nat)
    (nullifyingKey token boundParamsHash : Nat) (root : Term) (treeNumber : Nat)
    (randomIn valueIn : Fin N → Nat) (leavesIndices : Fin N → Nat)
    (pathElements : Fin N → List (Term × Bool)) (npkOut : Fin M → Term) (valueOut : Fin M → Nat)
    (hN : N ≤ 8) (hM : M ≤ 4)
    (hRoot : root ∈ s.rootsAt' treeNumber)
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
    (hFresh : ∀ i, nullifier (Term.val nullifyingKey) (leavesIndices i) ∉ s.spent treeNumber)
    {rest : List ((Nat × Nat) × CommitmentPreimage)}
    (hLive : removeAll (s.live token)
        (List.ofFn fun i =>
          ((treeNumber, leavesIndices i),
            (⟨npk (masterPublicKey publicKey nullifyingKey) (randomIn i), token, valueIn i⟩ :
              CommitmentPreimage)))
        = some rest) :
    ∃ s', Step s s' := by
  let pub : TransactPublic N M :=
    { merkleRoot := root, boundParamsHash := boundParamsHash,
      nullifiers := fun i => nullifier (Term.val nullifyingKey) (leavesIndices i),
      commitmentsOut := fun j => commitment (npkOut j) token (valueOut j) }
  let w : TransactWitness N M :=
    { token := token, publicKey := publicKey,
      signature := hSig.sign publicKey (msgHashOf pub), nullifyingKey := nullifyingKey,
      randomIn := randomIn, valueIn := valueIn, pathElements := pathElements,
      leavesIndices := leavesIndices, npkOut := npkOut, valueOut := valueOut }
  have hC : Constrained w pub :=
    { pathLen := hPathLen, merkle := hMerkle, nullifiers := fun _ => rfl,
      outputs := fun _ => rfl, rangeIn := hRangeIn, rangeOut := hRangeOut,
      balance := congrArg (· % p) hBalance,
      distinct := ofFn_pairwise_ne leavesIndices hDistinctLeaves,
      sig := hSig.signSound publicKey (msgHashOf pub) }
  have hV : VerifyAccepts pub := hComplete.complete hC
  obtain ⟨spent', hMark⟩ := markSpent_succeeds
    (by
      have hmap := distinct_leaves_distinct_nullifiers (Term.val nullifyingKey) (List.ofFn leavesIndices)
        hDistinctLeaves
      have heq : (List.ofFn leavesIndices).map (nullifier (Term.val nullifyingKey))
          = List.ofFn (fun i => nullifier (Term.val nullifyingKey) (leavesIndices i)) := List.map_ofFn
      rwa [heq] at hmap)
    (show ∀ n ∈ List.ofFn (fun i => nullifier (Term.val nullifyingKey) (leavesIndices i)),
        n ∉ s.spent treeNumber by
      intro n hn
      obtain ⟨i, hi⟩ := List.mem_ofFn.mp hn
      rw [← hi]
      exact hFresh i)
  refine ⟨_, Step.transact w pub treeNumber hN hM hC
    (List.ofFn fun j => (⟨npkOut j, token, valueOut j⟩ : CommitmentPreimage)) [] rest spent'
    [] [] hRoot (by simp [transactAllOutputs, w])
    (by simp) hLive hMark (List.nil_sublist _) (by simp)⟩

/-- **Can happen: an unshield succeeds.** The degenerate single-output shape of
    `transact_can_happen`: a real key holder spends `N` genuinely-held, genuinely-live
    notes at tree `treeNumber` and the circuit's one output is the unshield payout
    itself (`newNotes := []`, the entire spent value becomes the unshield payout) —
    `_validateTransaction`'s unshield checks (TransactModule.sol:295-331; see the
    Zokyo 2022-12-21 finding #1 cited at `Step.transact`) are exactly what licenses
    reading the circuit's one output as the payout amount. -/
theorem unshield_can_happen {s : PoolState} (hComplete : TransactProofCompleteness)
    (hSig : HonestSignature) {N : Nat} (publicKey : Nat × Nat)
    (nullifyingKey token boundParamsHash : Nat) (root : Term) (treeNumber : Nat)
    (randomIn valueIn : Fin N → Nat) (leavesIndices : Fin N → Nat)
    (pathElements : Fin N → List (Term × Bool)) (npkOut : Term) (valueOut : Nat)
    (hN : N ≤ 8)
    (hRoot : root ∈ s.rootsAt' treeNumber)
    (hValuePos : 0 < valueOut)
    (hPathLen : ∀ i, (pathElements i).length = 16)
    (hMerkle : ∀ i,
      merkleRoot
        (commitment (npk (masterPublicKey publicKey nullifyingKey) (randomIn i)) token
          (valueIn i))
        (pathElements i) = root)
    (hRangeIn : ∀ i, RangeChecked120 (valueIn i)) (hRangeOut : RangeChecked120 valueOut)
    (hBalance : listSum (List.ofFn valueIn) = valueOut)
    (hDistinctLeaves : (List.ofFn leavesIndices).Pairwise (· ≠ ·))
    (hFresh : ∀ i, nullifier (Term.val nullifyingKey) (leavesIndices i) ∉ s.spent treeNumber)
    {rest : List ((Nat × Nat) × CommitmentPreimage)}
    (hLive : removeAll (s.live token)
        (List.ofFn fun i =>
          ((treeNumber, leavesIndices i),
            (⟨npk (masterPublicKey publicKey nullifyingKey) (randomIn i), token, valueIn i⟩ :
              CommitmentPreimage)))
        = some rest) :
    ∃ s', Step s s' := by
  let pub : TransactPublic N 1 :=
    { merkleRoot := root, boundParamsHash := boundParamsHash,
      nullifiers := fun i => nullifier (Term.val nullifyingKey) (leavesIndices i),
      commitmentsOut := fun _ => commitment npkOut token valueOut }
  let w : TransactWitness N 1 :=
    { token := token, publicKey := publicKey,
      signature := hSig.sign publicKey (msgHashOf pub), nullifyingKey := nullifyingKey,
      randomIn := randomIn, valueIn := valueIn, pathElements := pathElements,
      leavesIndices := leavesIndices, npkOut := fun _ => npkOut, valueOut := fun _ => valueOut }
  have hBalance1 : listSum (List.ofFn w.valueIn) = listSum (List.ofFn w.valueOut) := by
    simp [w, List.ofFn_succ, List.ofFn_zero, listSum, hBalance]
  have hC : Constrained w pub :=
    { pathLen := hPathLen, merkle := hMerkle, nullifiers := fun _ => rfl,
      outputs := fun _ => rfl, rangeIn := hRangeIn, rangeOut := fun _ => hRangeOut,
      balance := congrArg (· % p) hBalance1,
      distinct := ofFn_pairwise_ne leavesIndices hDistinctLeaves,
      sig := hSig.signSound publicKey (msgHashOf pub) }
  have hV : VerifyAccepts pub := hComplete.complete hC
  have _ := hValuePos
  obtain ⟨spent', hMark⟩ := markSpent_succeeds
    (by
      have hmap := distinct_leaves_distinct_nullifiers (Term.val nullifyingKey) (List.ofFn leavesIndices)
        hDistinctLeaves
      have heq : (List.ofFn leavesIndices).map (nullifier (Term.val nullifyingKey))
          = List.ofFn (fun i => nullifier (Term.val nullifyingKey) (leavesIndices i)) := List.map_ofFn
      rwa [heq] at hmap)
    (show ∀ n ∈ List.ofFn (fun i => nullifier (Term.val nullifyingKey) (leavesIndices i)),
        n ∉ s.spent treeNumber by
      intro n hn
      obtain ⟨i, hi⟩ := List.mem_ofFn.mp hn
      rw [← hi]
      exact hFresh i)
  refine ⟨_, Step.transact w pub treeNumber hN (by omega) hC []
    (List.ofFn fun (_ : Fin 1) => (⟨npkOut, token, valueOut⟩ : CommitmentPreimage)) rest
    spent' [] [] hRoot
    (by simp [transactAllOutputs, w]) (by simp) hLive hMark (List.nil_sublist _) (by simp)⟩

/-- **Can happen: an owned transact succeeds.** Directly wires an owned witness,
    constructed exactly as `ArmadaLean.PoolOwned.owned_spend_can_happen` builds one
    (inlined here, not obtained from that theorem's existential, for the same
    definitional-transparency reason as `transact_can_happen`), into
    `Step.transactOwned`: `hLive` supplies the ghost liveness precondition, keyed by
    the exact `(treeNumber, leaf position)` pairs the owner's notes sit at (the
    model's own record of what it minted for them, and where), `hN`/`hM` the
    registered-shape bound, `caller`/`hCaller` the authorization check
    (`ArmadaLean.PoolSafety.transactOwned_spends_only_owned` is the matching safety
    theorem). An owned transact can pay out to any recipient's own note key, not only
    re-mint notes to itself (module comment, `Step.transactOwned`), so this witness
    supplies no owned-random disclosure for the new outputs (`ownedOutputs := []`) —
    a disclosed, contract-owned output is a separate, later act
    (`ArmadaLean.PoolOwned`'s module comment on `OwnedDisclosure`), not a precondition
    for the spend itself to succeed. -/
theorem owned_transact_can_happen {s : PoolState} (hComplete : OwnedProofCompleteness)
    {N M : Nat} (ownerField : Term) (token boundParamsHash : Nat) (root : Term)
    (treeNumber : Nat)
    (randomIn valueIn : Fin N → Nat) (leavesIndices : Fin N → Nat)
    (pathElements : Fin N → List (Term × Bool)) (npkOut : Fin M → Term) (valueOut : Fin M → Nat)
    (hN : N ≤ 8) (hM : M ≤ 4)
    (hRoot : root ∈ s.rootsAt' treeNumber)
    (hPathLen : ∀ i, (pathElements i).length = 16)
    (hMerkle : ∀ i,
      merkleRoot (commitment (npk ownerField (randomIn i)) token (valueIn i))
        (pathElements i) = root)
    (hRangeIn : ∀ i, RangeChecked120 (valueIn i))
    (hRangeOut : ∀ j, RangeChecked120 (valueOut j))
    (hBalance : listSum (List.ofFn valueIn) = listSum (List.ofFn valueOut))
    (hDistinctLeaves : (List.ofFn leavesIndices).Pairwise (· ≠ ·))
    (hFresh : ∀ i, nullifier ownerField (leavesIndices i) ∉ s.spent treeNumber)
    (hOutputsNonZero : ∀ j, npkOut j ≠ Term.val 0)
    (caller : Term) (hCaller : caller = ownerField)
    {rest : List ((Nat × Nat) × CommitmentPreimage)}
    (hLive : removeAll (s.live token)
        (List.ofFn fun i =>
          ((treeNumber, leavesIndices i),
            (⟨npk ownerField (randomIn i), token, valueIn i⟩ : CommitmentPreimage)))
        = some rest) :
    ∃ s', Step s s' := by
  let w : TransactOwnedWitness N M :=
    { token := token, randomIn := randomIn, valueIn := valueIn, pathElements := pathElements,
      leavesIndices := leavesIndices, npkOut := npkOut, valueOut := valueOut }
  let pub : TransactOwnedPublic N M :=
    { merkleRoot := root, boundParamsHash := boundParamsHash,
      nullifiers := fun i => nullifier ownerField (leavesIndices i),
      commitmentsOut := fun j => commitment (npkOut j) token (valueOut j),
      ownerField := ownerField }
  have hC : OwnedConstrained w pub :=
    { pathLen := hPathLen, merkle := hMerkle, nullifiers := fun _ => rfl,
      outputs := fun _ => rfl, rangeIn := hRangeIn, rangeOut := hRangeOut,
      balance := congrArg (· % p) hBalance }
  have hV : VerifyOwnedAccepts pub := hComplete.complete hC
  obtain ⟨spent', hMark⟩ := markSpent_succeeds
    (by
      have hmap := distinct_leaves_distinct_nullifiers ownerField (List.ofFn leavesIndices)
        hDistinctLeaves
      have heq : (List.ofFn leavesIndices).map (nullifier ownerField)
          = List.ofFn (fun i => nullifier ownerField (leavesIndices i)) := List.map_ofFn
      rwa [heq] at hmap)
    (show ∀ n ∈ List.ofFn (fun i => nullifier ownerField (leavesIndices i)),
        n ∉ s.spent treeNumber by
      intro n hn
      obtain ⟨i, hi⟩ := List.mem_ofFn.mp hn
      rw [← hi]
      exact hFresh i)
  refine ⟨_, Step.transactOwned w pub treeNumber hN hM hC caller hCaller rest spent' []
    hRoot hLive hMark ?_ (fun x hx => absurd hx (List.not_mem_nil))⟩
  intro j hz
  exact hOutputsNonZero j hz.1

/-! ### Every inserted leaf has a Merkle witness to a root the pool produced -/

/-- One step either leaves tree `tn`'s leaves and roots both unchanged, or appends to
    `leavesAt' tn` and pushes exactly `ArmadaLean.Merkle.treeRoot TreeDepth` of the
    result to `rootsAt' tn` — `insertResult_rootsAt_matches_leavesAt`, applied to
    whichever batch and tree a `Step` constructor targets. A standalone wrapper
    (states inferred from `hstep`, as `step_rootsAt_shape` already is) so
    `reachable_rootAt_matches_leavesAt`'s induction never needs to name the previous
    state by hand. -/
theorem step_leavesAt_rootsAt_matches {s s' : PoolState} (hstep : Step s s') (tn : Nat) :
    (s'.leavesAt' tn = s.leavesAt' tn ∧ s'.rootsAt' tn = s.rootsAt' tn) ∨
      s'.rootsAt' tn = treeRoot TreeDepth (s'.leavesAt' tn) :: s.rootsAt' tn := by
  cases hstep with
  | shield token grossAmount feeBP npk hNotPaused hValue hFeeBP hRange =>
    exact insertResult_rootsAt_matches_leavesAt s.closedTrees s.leaves s.roots
      [hashCommitment (⟨npk, token, shieldBase feeBP grossAmount⟩ : CommitmentPreimage)] tn
  | transact w pub treeNumber hN hM hC newNotes unshieldTail rest spent' records ownedRecords
      hRoot hSplit hUnshieldLen hRemove hNullify hRecords hOwnedRecords =>
    exact insertResult_rootsAt_matches_leavesAt s.closedTrees s.leaves s.roots
      (newNotes.map hashCommitment) tn
  | transactOwned w pub treeNumber hN hM hC caller hCaller rest spent' ownedOutputs
      hRoot hRemove hNullify hNonZero hOwnedOutputs =>
    exact insertResult_rootsAt_matches_leavesAt s.closedTrees s.leaves s.roots
      ((ownedNewNotes w).map hashCommitment) tn
  | admin shieldsPaused =>
    exact Or.inl ⟨rfl, rfl⟩

/-- **The root most recently pushed to a tree always matches that tree's actual leaf
    list — for every tree the pool has actually inserted a leaf into.** Every
    reachable state's tree-`tn` head root is `ArmadaLean.Merkle.treeRoot TreeDepth` of
    its own `leavesAt' tn` — never a free choice (`step_leavesAt_rootsAt_matches`),
    proved by induction on `Reachable`. Stated as a disjunction with "tree `tn` has no
    leaves at all" to cover a tree number no step has reached yet (the `getD`-default
    convention, Pool.lean's module comment: a tree the pool has never rolled into has
    empty `leavesAt'`) — `leaf_has_merkle_witness` rules that case out directly via its
    own in-range hypothesis. -/
theorem reachable_rootAt_matches_leavesAt {s : PoolState} (h : Reachable s) (tn : Nat) :
    s.leavesAt' tn = [] ∨ treeRoot TreeDepth (s.leavesAt' tn) ∈ s.rootsAt' tn := by
  induction h with
  | genesis =>
    left; simp [genesis, PoolState.leavesAt', PoolState.leavesAt]
  | step _ hstep ih =>
    rcases step_leavesAt_rootsAt_matches hstep tn with ⟨hl, hr⟩ | hr
    · rw [hl, hr]; exact ih
    · right; rw [hr]; exact List.mem_cons_self

/-- One step's new batch is always within capacity (`1` for a shield, `≤ M ≤ 4` for a
    transact/transactOwned), so `insertResult_leavesAt_capacity` keeps every tree
    within capacity across the step, given it held before. A standalone wrapper
    (states inferred from `hstep`) so `reachable_leavesAt_capacity`'s induction never
    needs to name the previous state by hand. -/
theorem step_leavesAt_capacity_preserved {s s' : PoolState} (hstep : Step s s')
    (hOldCap : ∀ k, (s.leavesAt' k).length ≤ 2 ^ TreeDepth) (tn : Nat) :
    (s'.leavesAt' tn).length ≤ 2 ^ TreeDepth := by
  cases hstep with
  | shield token grossAmount feeBP npk hNotPaused hValue hFeeBP hRange =>
    exact insertResult_leavesAt_capacity s.closedTrees s.leaves s.roots
      [hashCommitment (⟨npk, token, shieldBase feeBP grossAmount⟩ : CommitmentPreimage)] tn
      (by simp; unfold TreeDepth; omega) hOldCap
  | transact w pub treeNumber hN hM hC newNotes unshieldTail rest spent' records ownedRecords
      hRoot hSplit hUnshieldLen hRemove hNullify hRecords hOwnedRecords =>
    have hlenEq := congrArg List.length hSplit
    unfold transactAllOutputs at hlenEq
    simp only [List.length_ofFn, List.length_append] at hlenEq
    have hlen : newNotes.length ≤ 4 := by omega
    exact insertResult_leavesAt_capacity s.closedTrees s.leaves s.roots
      (newNotes.map hashCommitment) tn (by simp; unfold TreeDepth; omega) hOldCap
  | transactOwned w pub treeNumber hN hM hC caller hCaller rest spent' ownedOutputs
      hRoot hRemove hNullify hNonZero hOwnedOutputs =>
    have hlen : (ownedNewNotes w).length ≤ 4 := by
      unfold ownedNewNotes
      simp only [List.length_ofFn]
      omega
    exact insertResult_leavesAt_capacity s.closedTrees s.leaves s.roots
      ((ownedNewNotes w).map hashCommitment) tn (by simp; unfold TreeDepth; omega) hOldCap
  | admin shieldsPaused =>
    exact hOldCap tn

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
  | genesis =>
    intro tn
    simp only [genesis, PoolState.leavesAt', PoolState.leavesAt]
    by_cases htn : tn = 0 <;> simp [htn]
  | step _ hstep ih =>
    exact step_leavesAt_capacity_preserved hstep ih

/--
**Every leaf the pool has ever inserted into a tree has a real Merkle witness to a
root the pool produced for that tree.** For any reachable state `s`, tree `tn` and
any in-range leaf position `i`, the path `ArmadaLean.Merkle.treePath TreeDepth
(s.leavesAt' tn) i` is a genuine membership proof: folding it from the leaf at
position `i` reconstructs `treeRoot TreeDepth (s.leavesAt' tn)` (`treePath_correct`,
`reachable_leavesAt_capacity` for the depth bound), and that root is itself one of the
pool's own, `s.rootsAt' tn` (`reachable_rootAt_matches_leavesAt`) — the current root
of that tree, in the sense of "the one current when the leaf was inserted, or a later
one", since `rootsAt' tn` never expires an entry (`PrivacyPoolStorage.rootHistory`,
PrivacyPoolStorage.sol:171) and every later step only ever prepends to it
(`step_rootsAt_shape`): the witness built from the LATEST leaf list and root always
verifies against a root the contract still accepts, for every leaf inserted so far
into that tree, not only the ones inserted in the step that produced that exact root.
This holds in every tree the pool has ever rolled over into, not only the current
one. -/
theorem leaf_has_merkle_witness {s : PoolState} (h : Reachable s) (tn : Nat)
    {i : Nat} (hi : i < (s.leavesAt' tn).length) :
    merkleRoot ((s.leavesAt' tn).getD i (Term.val 0)) (treePath TreeDepth (s.leavesAt' tn) i) =
        treeRoot TreeDepth (s.leavesAt' tn) ∧
      treeRoot TreeDepth (s.leavesAt' tn) ∈ s.rootsAt' tn := by
  have hcap := reachable_leavesAt_capacity h tn
  refine ⟨treePath_correct TreeDepth (s.leavesAt' tn) i (by omega), ?_⟩
  rcases reachable_rootAt_matches_leavesAt h tn with hempty | hmatch
  · rw [hempty] at hi; exact absurd hi (by simp)
  · exact hmatch

/-! ### A live owned note with a recorded preimage has a constructible spend witness -/

/--
**A live owned note with a recorded preimage has a constructible `OwnedConstrained`
spend witness, built entirely from public data.** Given `N` input notes whose recorded
preimages (`preimages`, exactly what `PoolState.preimageOf` records for every
disclosed output — public: every entry there came from a `shield`/`transact`
/`transactOwned` event, PrivacyPoolStorage.preimageOf, PrivacyPoolStorage.sol:248) sit
at known leaf positions in a leaf list `leaves` (`hLeafValue`, public: every leaf is a
commitment the pool has itself emitted — callers instantiate `leaves := s.leavesAt'
tn` for whichever tree `tn` holds the note, so this theorem is tree-agnostic by
construction, true against every tree the pool has ever rolled into), and each is on
record as a contract-owned note belonging to `ownerField` in the public
`ownedRandomOf` registry (`hOwned`, `ArmadaLean.PoolOwned`'s module comment on
`OwnedDisclosure` — the approved design this models), a satisfying `OwnedConstrained`
witness/public pair exists — its Merkle path is `ArmadaLean.Merkle.treePath TreeDepth
leaves`, computed, not a free choice, and `treePath_correct` is exactly what proves it
satisfies `OwnedConstrained.merkle`.

**No non-public value is needed.** The earlier form of this theorem took `randomIn :
Fin N → Nat` as a free input — a value nothing in the OLD registry shape could ever
produce, since the real contract records no random at all (`ArmadaLean.PoolOwned`'s
module comment on `OwnedDisclosure`, citing `PoolTypes.sol:79-83` and
`TransactModule.sol:590-604`). With the approved design's second registry,
`ownedRandomOf`, the random is itself public data: `hOwned`'s existential is resolved
internally, by `choose`, from the registry lookup `ownedRandomOf (hashCommitment
(preimages i))`, never supplied externally. -/
theorem owned_spend_witness_exists {N M : Nat}
    (ownerField : Term) (token boundParamsHash : Nat)
    (preimages : Fin N → CommitmentPreimage)
    (leavesIndices : Fin N → Nat) (leaves : List Term)
    (ownedRandomOf : OwnedRandomRegistry)
    (hToken : ∀ i, (preimages i).token = token)
    (hOwned : ∀ i, ∃ r, ownedRandomOf (hashCommitment (preimages i)) = some ⟨ownerField, r⟩ ∧
      npk ownerField r = (preimages i).npk)
    (hLeafIndex : ∀ i, leavesIndices i < 2 ^ TreeDepth)
    (hLeafValue : ∀ i, leaves.getD (leavesIndices i) (Term.val 0) = hashCommitment (preimages i))
    (npkOut : Fin M → Term) (valueOut : Fin M → Nat)
    (hRangeIn : ∀ i, RangeChecked120 (preimages i).value)
    (hRangeOut : ∀ j, RangeChecked120 (valueOut j))
    (hBalance : listSum (List.ofFn fun i => (preimages i).value) = listSum (List.ofFn valueOut)) :
    ∃ (w : TransactOwnedWitness N M) (pub : TransactOwnedPublic N M),
      OwnedConstrained w pub ∧
      pub.merkleRoot = treeRoot TreeDepth leaves ∧
      pub.ownerField = ownerField ∧
      w.token = token ∧
      (∀ i, w.valueIn i = (preimages i).value) ∧
      (∀ i, commitment (npk ownerField (w.randomIn i)) w.token (w.valueIn i) =
        hashCommitment (preimages i)) := by
  let randomIn : Fin N → Nat := fun i => (hOwned i).choose
  have hRandomReg : ∀ i, ownedRandomOf (hashCommitment (preimages i)) =
      some ⟨ownerField, randomIn i⟩ := fun i => (hOwned i).choose_spec.1
  have hRandomNpk : ∀ i, npk ownerField (randomIn i) = (preimages i).npk :=
    fun i => (hOwned i).choose_spec.2
  let w : TransactOwnedWitness N M :=
    { token := token, randomIn := randomIn, valueIn := fun i => (preimages i).value,
      pathElements := fun i => treePath TreeDepth leaves (leavesIndices i),
      leavesIndices := leavesIndices, npkOut := npkOut, valueOut := valueOut }
  let pub : TransactOwnedPublic N M :=
    { merkleRoot := treeRoot TreeDepth leaves, boundParamsHash := boundParamsHash,
      nullifiers := fun i => nullifier ownerField (leavesIndices i),
      commitmentsOut := fun j => commitment (npkOut j) token (valueOut j),
      ownerField := ownerField }
  have hcommit : ∀ i : Fin N, hashCommitment (preimages i) =
      commitment (npk ownerField (randomIn i)) token ((preimages i).value) := by
    intro i
    unfold hashCommitment
    rw [← hRandomNpk i, hToken i]
  have hmerkle : ∀ i : Fin N,
      merkleRoot
        (commitment (npk ownerField (randomIn i)) token ((preimages i).value))
        (treePath TreeDepth leaves (leavesIndices i)) = treeRoot TreeDepth leaves := by
    intro i
    rw [← hcommit i, ← hLeafValue i]
    exact treePath_correct TreeDepth leaves (leavesIndices i) (hLeafIndex i)
  have hC : OwnedConstrained w pub :=
    { pathLen := fun i => treePath_length TreeDepth leaves (leavesIndices i),
      merkle := hmerkle, nullifiers := fun _ => rfl, outputs := fun _ => rfl,
      rangeIn := hRangeIn, rangeOut := hRangeOut, balance := congrArg (· % p) hBalance }
  exact ⟨w, pub, hC, rfl, rfl, rfl, fun _ => rfl, fun i => (hcommit i).symm⟩

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

theorem genesis_live_spent_invariant : LiveSpentInvariant genesis := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> intro <;> simp [genesis]

theorem step_preserves_live_spent_invariant {s s' : PoolState} (ih : LiveSpentInvariant s)
    (hstep : Step s s') : LiveSpentInvariant s' := by
  obtain ⟨ih1, ih2, ih3, ih4, ih5⟩ := ih
  simp only [PoolState.leavesAt'] at ih1 ih3
  cases hstep with
  | shield token grossAmount feeBP npk hNotPaused hValue hFeeBP hRange =>
    have hpos0eq := insertStartPos_eq_leavesAt_length s.closedTrees s.leaves s.roots 1
    have hlenge := fun tn => insertResult_leavesAt_length_ge s.closedTrees s.leaves s.roots
      [hashCommitment (⟨npk, token, shieldBase feeBP grossAmount⟩ : CommitmentPreimage)] tn
    have htarget := insertResult_leavesAt_target_length s.closedTrees s.leaves s.roots
      [hashCommitment (⟨npk, token, shieldBase feeBP grossAmount⟩ : CommitmentPreimage)]
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
        have hlt := ih1 token (insertTreeNumber s.closedTrees s.leaves 1) (insertStartPos s.leaves 1)
          (⟨npk, token, shieldBase feeBP grossAmount⟩ : CommitmentPreimage) hmem
        rw [← hpos0eq] at hlt
        omega
      · simp only [if_neg ht]
        exact ih5 t
  | transact w pub treeNumber hN hM hC newNotes unshieldTail rest spent' records ownedRecords
      hRoot hSplit hUnshieldLen hRemove hNullify hRecords hOwnedRecords =>
    have hpos0eq := insertStartPos_eq_leavesAt_length s.closedTrees s.leaves s.roots newNotes.length
    have hlenge := fun tn' => insertResult_leavesAt_length_ge s.closedTrees s.leaves s.roots
      (newNotes.map hashCommitment) tn'
    have htarget := insertResult_leavesAt_target_length s.closedTrees s.leaves s.roots
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
              have hge2 : (PoolState.leavesAt s.closedTrees s.leaves s.roots treeNumber).length ≤ pos := by
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
  | transactOwned w pub treeNumber hN hM hC caller hCaller rest spent' ownedOutputs
      hRoot hRemove hNullify hNonZero hOwnedOutputs =>
    have hpos0eq := insertStartPos_eq_leavesAt_length s.closedTrees s.leaves s.roots (ownedNewNotes w).length
    have hlenge := fun tn' => insertResult_leavesAt_length_ge s.closedTrees s.leaves s.roots
      ((ownedNewNotes w).map hashCommitment) tn'
    have htarget := insertResult_leavesAt_target_length s.closedTrees s.leaves s.roots
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
              have hge2 : (PoolState.leavesAt s.closedTrees s.leaves s.roots treeNumber).length ≤ pos := by
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
  | admin shieldsPaused =>
    exact ⟨ih1, ih2, ih3, ih4, ih5⟩

theorem reachable_live_spent_invariant {s : PoolState} (h : Reachable s) :
    LiveSpentInvariant s := by
  induction h with
  | genesis => exact genesis_live_spent_invariant
  | step _ hstep ih => exact step_preserves_live_spent_invariant ih hstep

/--
**A live note's nullifier is not in `spent`.** For any reachable state, any live entry
`((tn, pos), pre) ∈ s.live t` and any nullifying key `nk`, `nullifier nk pos` is not
among tree `tn`'s spent nullifiers. The adjudicator's own payout spend needs exactly
this: it already knows its own `(treeNumber, position)` for a note it holds live, and
this is what shows `markSpent` will accept the nullifier it derives for that spend, not
revert it as already-spent. Proved from the ghost invariant `LiveSpentInvariant`: a
position still live was never named by any earlier `transact`/`transactOwned` (its
`hRemove`/`hNullify` are taken from the same witness in the same step,
`ArmadaLean.Pool.Step.transact`/`.transactOwned`'s own construction, so a spend that
named this position would have removed it from `live` at that same step — and
`removeAll_disjoint`, keyed by `LiveSpentInvariant`'s no-duplicate-entry fact, rules
out it surviving that removal under a different disguise). -/
theorem live_note_unspent {s : PoolState} (h : Reachable s) (t tn pos : Nat)
    (pre : CommitmentPreimage) (hmem : ((tn, pos), pre) ∈ s.live t) (nk : Term) :
    nullifier nk pos ∉ s.spent tn :=
  (reachable_live_spent_invariant h).2.2.2.1 t tn pos pre hmem nk

/-! ### A leaf, once inserted, never moves -/

/-- One step either leaves tree `tn`'s leaves unchanged, or appends to them —
    `insertResult_leavesAt_length_ge`/`_stable` give the two facts `leaf_stable` needs
    (monotone length, unchanged value at an already-in-range position), applied to
    whichever batch and tree a `Step` constructor targets. -/
theorem step_leavesAt_stable {s s' : PoolState} (hstep : Step s s') (tn pos : Nat) (d : Term)
    (hpos : pos < (s.leavesAt' tn).length) :
    pos < (s'.leavesAt' tn).length ∧
      (s'.leavesAt' tn).getD pos d = (s.leavesAt' tn).getD pos d := by
  cases hstep with
  | shield token grossAmount feeBP npk hNotPaused hValue hFeeBP hRange =>
    refine ⟨?_, ?_⟩
    · exact Nat.lt_of_lt_of_le hpos
        (insertResult_leavesAt_length_ge s.closedTrees s.leaves s.roots
          [hashCommitment (⟨npk, token, shieldBase feeBP grossAmount⟩ : CommitmentPreimage)] tn)
    · exact insertResult_leavesAt_stable s.closedTrees s.leaves s.roots
        [hashCommitment (⟨npk, token, shieldBase feeBP grossAmount⟩ : CommitmentPreimage)] tn pos d hpos
  | transact w pub treeNumber hN hM hC newNotes unshieldTail rest spent' records ownedRecords
      hRoot hSplit hUnshieldLen hRemove hNullify hRecords hOwnedRecords =>
    refine ⟨?_, ?_⟩
    · exact Nat.lt_of_lt_of_le hpos
        (insertResult_leavesAt_length_ge s.closedTrees s.leaves s.roots
          (newNotes.map hashCommitment) tn)
    · exact insertResult_leavesAt_stable s.closedTrees s.leaves s.roots
        (newNotes.map hashCommitment) tn pos d hpos
  | transactOwned w pub treeNumber hN hM hC caller hCaller rest spent' ownedOutputs
      hRoot hRemove hNullify hNonZero hOwnedOutputs =>
    refine ⟨?_, ?_⟩
    · exact Nat.lt_of_lt_of_le hpos
        (insertResult_leavesAt_length_ge s.closedTrees s.leaves s.roots
          ((ownedNewNotes w).map hashCommitment) tn)
    · exact insertResult_leavesAt_stable s.closedTrees s.leaves s.roots
        ((ownedNewNotes w).map hashCommitment) tn pos d hpos
  | admin shieldsPaused =>
    exact ⟨hpos, rfl⟩

/--
**A leaf, once inserted at a position, never changes in any later reachable state.**
For any `ReachableFrom s s'` and any position already in range at `s` (`pos <
(s.leavesAt' tn).length`), it stays in range at `s'` and carries the exact same leaf
value — leaves only ever append, never mutate or shrink
(`insertResult_leavesAt_length_ge`/`_stable`, `Step`'s own construction: every
constructor either leaves a tree's leaves untouched or extends them). Combined with
`shield_creates_exactly`/the `Step.transact`/`.transactOwned` outputs' own positions
(each constructor reports the exact `(treeNumber, position)` its outputs land at), this
ties a holding's recorded position to its commitment for the rest of the pool's
history: once minted, a note's leaf is immutable. -/
theorem leaf_stable {s s' : PoolState} (h : ReachableFrom s s') (tn pos : Nat) (d : Term)
    (hpos : pos < (s.leavesAt' tn).length) :
    pos < (s'.leavesAt' tn).length ∧
      (s'.leavesAt' tn).getD pos d = (s.leavesAt' tn).getD pos d := by
  induction h with
  | refl => exact ⟨hpos, rfl⟩
  | step _ hstep ih =>
    obtain ⟨ihlen, iheq⟩ := ih
    obtain ⟨hlen2, heq2⟩ := step_leavesAt_stable hstep tn pos d ihlen
    exact ⟨hlen2, heq2.trans iheq⟩

/-! ### A live entry's position names the leaf that holds its commitment -/

/-- One step preserves "every live entry's position holds its own commitment as a
    leaf": a surviving entry's leaf is unchanged (`insertResult_leavesAt_stable`,
    using `ihrange` for the in-range precondition), and a freshly-inserted entry's
    leaf is exactly its own hash by construction
    (`insertResult_leavesAt_new_matches`/`withTreePositionsFrom_leaf_matches`). A
    standalone wrapper (states inferred from `hstep`) so
    `reachable_live_leaf_matches`'s induction never needs to name the previous state
    by hand. -/
theorem step_live_leaf_matches {s s' : PoolState} (hstep : Step s s')
    (ihmatch : ∀ t tn pos pre, ((tn, pos), pre) ∈ s.live t →
      (s.leavesAt' tn).getD pos (Term.val 0) = hashCommitment pre)
    (ihrange : ∀ t tn pos pre, ((tn, pos), pre) ∈ s.live t → pos < (s.leavesAt' tn).length) :
    ∀ t tn pos pre, ((tn, pos), pre) ∈ s'.live t →
      (s'.leavesAt' tn).getD pos (Term.val 0) = hashCommitment pre := by
  cases hstep with
  | shield token grossAmount feeBP npk hNotPaused hValue hFeeBP hRange =>
    intro t tn pos pre hmem
    by_cases ht : t = token
    · subst t
      simp only at hmem
      rcases List.eq_or_mem_of_mem_cons hmem with heq | hmem
      · obtain ⟨base, hbaselen, hbase⟩ := insertResult_leavesAt_new_matches s.closedTrees s.leaves
            s.roots [hashCommitment (⟨npk, token, shieldBase feeBP grossAmount⟩ : CommitmentPreimage)]
            (insertTreeNumber s.closedTrees s.leaves 1) rfl
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
        rw [insertResult_leavesAt_stable s.closedTrees s.leaves s.roots
          [hashCommitment (⟨npk, token, shieldBase feeBP grossAmount⟩ : CommitmentPreimage)] tn pos
          (Term.val 0) hr]
        exact hmatch
    · simp only [if_neg ht] at hmem
      have hmatch := ihmatch t tn pos pre hmem
      have hr := ihrange t tn pos pre hmem
      dsimp only [PoolState.leavesAt']
      rw [insertResult_leavesAt_stable s.closedTrees s.leaves s.roots
        [hashCommitment (⟨npk, token, shieldBase feeBP grossAmount⟩ : CommitmentPreimage)] tn pos
        (Term.val 0) hr]
      exact hmatch
  | transact w pub treeNumber hN hM hC newNotes unshieldTail rest spent' records ownedRecords
      hRoot hSplit hUnshieldLen hRemove hNullify hRecords hOwnedRecords =>
    intro t tn pos pre hmem
    have hlenEq : (newNotes.map hashCommitment).length = newNotes.length := by simp
    by_cases ht : t = w.token
    · subst ht
      simp only at hmem
      rcases List.mem_append.mp hmem with hnew | hrest
      · have htn : insertTreeNumber s.closedTrees s.leaves newNotes.length =
            insertTreeNumber s.closedTrees s.leaves (newNotes.map hashCommitment).length := by
          rw [hlenEq]
        obtain ⟨base, hbaselen, hbase⟩ := insertResult_leavesAt_new_matches s.closedTrees s.leaves
            s.roots (newNotes.map hashCommitment)
            (insertTreeNumber s.closedTrees s.leaves (newNotes.map hashCommitment).length) rfl
        rw [← htn] at hbase
        rw [hlenEq] at hbaselen
        have htn' := withTreePositionsFrom_treeNumber _ _ _ _ hnew
        simp only at htn'
        have hleaf := withTreePositionsFrom_leaf_matches hashCommitment base
          (insertTreeNumber s.closedTrees s.leaves newNotes.length)
          (insertStartPos s.leaves newNotes.length) newNotes hbaselen (Term.val 0) ((tn, pos), pre) hnew
        dsimp only [PoolState.leavesAt']
        rw [htn', hbase]
        exact hleaf
      · have hmemold : ((tn, pos), pre) ∈ s.live w.token :=
          (removeAll_perm hRemove).mem_iff.mpr (List.mem_append_right _ hrest)
        have hmatch := ihmatch w.token tn pos pre hmemold
        have hr := ihrange w.token tn pos pre hmemold
        dsimp only [PoolState.leavesAt']
        rw [insertResult_leavesAt_stable s.closedTrees s.leaves s.roots
          (newNotes.map hashCommitment) tn pos (Term.val 0) hr]
        exact hmatch
    · simp only [if_neg ht] at hmem
      have hmatch := ihmatch t tn pos pre hmem
      have hr := ihrange t tn pos pre hmem
      dsimp only [PoolState.leavesAt']
      rw [insertResult_leavesAt_stable s.closedTrees s.leaves s.roots
        (newNotes.map hashCommitment) tn pos (Term.val 0) hr]
      exact hmatch
  | transactOwned w pub treeNumber hN hM hC caller hCaller rest spent' ownedOutputs
      hRoot hRemove hNullify hNonZero hOwnedOutputs =>
    intro t tn pos pre hmem
    have hlenEq : ((ownedNewNotes w).map hashCommitment).length = (ownedNewNotes w).length := by simp
    by_cases ht : t = w.token
    · subst ht
      simp only at hmem
      rcases List.mem_append.mp hmem with hnew | hrest
      · have htn : insertTreeNumber s.closedTrees s.leaves (ownedNewNotes w).length =
            insertTreeNumber s.closedTrees s.leaves ((ownedNewNotes w).map hashCommitment).length := by
          rw [hlenEq]
        obtain ⟨base, hbaselen, hbase⟩ := insertResult_leavesAt_new_matches s.closedTrees s.leaves
            s.roots ((ownedNewNotes w).map hashCommitment)
            (insertTreeNumber s.closedTrees s.leaves ((ownedNewNotes w).map hashCommitment).length) rfl
        rw [← htn] at hbase
        rw [hlenEq] at hbaselen
        have htn' := withTreePositionsFrom_treeNumber _ _ _ _ hnew
        simp only at htn'
        have hleaf := withTreePositionsFrom_leaf_matches hashCommitment base
          (insertTreeNumber s.closedTrees s.leaves (ownedNewNotes w).length)
          (insertStartPos s.leaves (ownedNewNotes w).length) (ownedNewNotes w) hbaselen (Term.val 0)
          ((tn, pos), pre) hnew
        dsimp only [PoolState.leavesAt']
        rw [htn', hbase]
        exact hleaf
      · have hmemold : ((tn, pos), pre) ∈ s.live w.token :=
          (removeAll_perm hRemove).mem_iff.mpr (List.mem_append_right _ hrest)
        have hmatch := ihmatch w.token tn pos pre hmemold
        have hr := ihrange w.token tn pos pre hmemold
        dsimp only [PoolState.leavesAt']
        rw [insertResult_leavesAt_stable s.closedTrees s.leaves s.roots
          ((ownedNewNotes w).map hashCommitment) tn pos (Term.val 0) hr]
        exact hmatch
    · simp only [if_neg ht] at hmem
      have hmatch := ihmatch t tn pos pre hmem
      have hr := ihrange t tn pos pre hmem
      dsimp only [PoolState.leavesAt']
      rw [insertResult_leavesAt_stable s.closedTrees s.leaves s.roots
        ((ownedNewNotes w).map hashCommitment) tn pos (Term.val 0) hr]
      exact hmatch
  | admin shieldsPaused =>
    exact ihmatch

/-- Every live entry at every reachable state still holds, at its own recorded
    position, a leaf that hashes to its own recorded preimage. -/
theorem reachable_live_leaf_matches {s : PoolState} (h : Reachable s) :
    ∀ t tn pos pre, ((tn, pos), pre) ∈ s.live t →
      (s.leavesAt' tn).getD pos (Term.val 0) = hashCommitment pre := by
  induction h with
  | genesis => intro t tn pos pre hmem; simp [genesis] at hmem
  | step hs hstep ih =>
    exact step_live_leaf_matches hstep ih (reachable_live_spent_invariant hs).1

/--
**A live entry's position names the leaf that holds its commitment.** For any
reachable state and any live entry `((tn, pos), pre) ∈ s.live t`, the leaf the pool
stored at `(tn, pos)` is exactly `hashCommitment pre` — never any other value.
Proved by induction: at the step that minted the entry, `insertResult_leavesAt`'s
exact equation pins the newly-appended leaf to the preimage that produced it
(`insertResult_leavesAt_new_matches`); at every later step while the entry stays
live, `leaf_stable`'s own mechanism (`insertResult_leavesAt_stable`) keeps the leaf
unchanged. Ties an adjudicator's holding — a recorded `(treeNumber, position)` and
preimage — to the actual on-chain leaf at that position, so a payout spend's Merkle
membership proof is the real leaf, not a forged one. -/
theorem live_leaf_matches {s : PoolState} (h : Reachable s) (t tn pos : Nat)
    (pre : CommitmentPreimage) (hmem : ((tn, pos), pre) ∈ s.live t) :
    (s.leavesAt' tn).getD pos (Term.val 0) = hashCommitment pre :=
  reachable_live_leaf_matches h t tn pos pre hmem

/-! ### Every live note's value fits the circuit's own field width -/

/-- Every live note's value is below `2 ^ 120`. -/
def LiveValuesBounded (s : PoolState) : Prop :=
  ∀ t p, p ∈ s.live t → p.2.value < 2 ^ 120

theorem genesis_live_values_bounded : LiveValuesBounded genesis := by
  intro t p hp
  simp [genesis] at hp

theorem step_preserves_live_values_bounded {s s' : PoolState} (ih : LiveValuesBounded s)
    (hstep : Step s s') : LiveValuesBounded s' := by
  cases hstep with
  | shield token grossAmount feeBP npk hNotPaused hValue hFeeBP hRange =>
    intro t p hp
    by_cases ht : t = token
    · subst t
      simp only at hp
      rcases List.eq_or_mem_of_mem_cons hp with heq | hp
      · rw [heq]
        exact rangeCheck120_sound _ hRange
      · exact ih token p hp
    · simp only [if_neg ht] at hp
      exact ih t p hp
  | transact w pub treeNumber hN hM hC newNotes unshieldTail rest spent' records ownedRecords
      hRoot hSplit hUnshieldLen hRemove hNullify hRecords hOwnedRecords =>
    intro t p hp
    by_cases ht : t = w.token
    · subst ht
      simp only at hp
      rcases List.mem_append.mp hp with hnew | hrest
      · have hqnew : p.2 ∈ newNotes := withTreePositionsFrom_snd_mem _ _ _ _ hnew
        have hmemall : p.2 ∈ transactAllOutputs w := by
          rw [hSplit]; exact List.mem_append_left _ hqnew
        unfold transactAllOutputs at hmemall
        obtain ⟨j, hj⟩ := List.mem_ofFn.mp hmemall
        rw [← hj]
        exact rangeCheck120_sound _ (hC.rangeOut j)
      · have hmemold : p ∈ s.live w.token :=
          (removeAll_perm hRemove).mem_iff.mpr (List.mem_append_right _ hrest)
        exact ih w.token p hmemold
    · simp only [if_neg ht] at hp
      exact ih t p hp
  | transactOwned w pub treeNumber hN hM hC caller hCaller rest spent' ownedOutputs
      hRoot hRemove hNullify hNonZero hOwnedOutputs =>
    intro t p hp
    by_cases ht : t = w.token
    · subst ht
      simp only at hp
      rcases List.mem_append.mp hp with hnew | hrest
      · have hqnew : p.2 ∈ ownedNewNotes w := withTreePositionsFrom_snd_mem _ _ _ _ hnew
        unfold ownedNewNotes at hqnew
        obtain ⟨j, hj⟩ := List.mem_ofFn.mp hqnew
        rw [← hj]
        exact rangeCheck120_sound _ (hC.rangeOut j)
      · have hmemold : p ∈ s.live w.token :=
          (removeAll_perm hRemove).mem_iff.mpr (List.mem_append_right _ hrest)
        exact ih w.token p hmemold
    · simp only [if_neg ht] at hp
      exact ih t p hp
  | admin shieldsPaused =>
    exact ih

/--
**Every note the pool records as live has a value below `2 ^ 120`.** The circuit range
checks each input/output value against `Num2Bits(120)` (`Constrained.rangeOut`
/`OwnedConstrained.rangeOut`, Transact.circom:125-129/TransactOwned.circom:117-121) and
a shield's note carries the same check as `Step.shield`'s own `hRange` hypothesis
(`CommitmentPreimage.value : uint120`, `PoolTypes.sol:79-83`) — so every value the pool
ever records as live already fits a `uint120`, pool-wide, not merely at the one step
that minted it. Proved by induction on `Reachable`, tracing a live note's value back to
the specific circuit output (`withTreePositionsFrom_snd_mem`) or shield amount that
produced it. -/
theorem live_values_lt_2pow120 {s : PoolState} (h : Reachable s) :
    LiveValuesBounded s := by
  induction h with
  | genesis => exact genesis_live_values_bounded
  | step _ hstep ih => exact step_preserves_live_values_bounded ih hstep
