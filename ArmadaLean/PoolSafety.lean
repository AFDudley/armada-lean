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

/-- The position-tagged counterpart of `value_ofFn_eq`: tagging each note with a leaf
    position (`transactSpentPositions`/`ownedSpentPositions`'s own shape) does not
    touch the value projection. -/
theorem value_ofFn_pos_eq {N : Nat} (pos : Fin N → Nat) (mk : Fin N → Term) (g : Fin N → Nat)
    (token : Nat) :
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
    (hN : N ≤ 8) (hM : M ≤ 4) (hC : Constrained w pub)
    {newNotes unshieldTail : List CommitmentPreimage}
    (hSplit : transactAllOutputs w = newNotes ++ unshieldTail) :
    listSum ((transactSpentPositions w).map (fun p => p.2.value)) =
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
    {pub : TransactOwnedPublic N M} (hN : N ≤ 8) (hM : M ≤ 4) (hC : OwnedConstrained w pub) :
    listSum ((ownedSpentPositions pub w).map (fun p => p.2.value)) =
      listSum ((ownedNewNotes w).map CommitmentPreimage.value) := by
  have hbal := transactOwned_value_conserved w pub hN hM hC
  unfold ownedSpentPositions ownedNewNotes
  rw [value_ofFn_pos_eq, value_ofFn_eq]
  exact hbal

theorem step_preserves_invariant {s s' : PoolState} (hinv : HeldInvariant s)
    (hstep : Step s s') : HeldInvariant s' := by
  cases hstep with
  | shield token grossAmount feeBP npk hNotPaused hValue hFeeBP hCapacity =>
    intro t
    by_cases ht : t = token
    · simp only [ht, if_pos]
      have hinv_t := hinv token
      simp only [List.map_cons, listSum]
      omega
    · simp only [if_neg ht]
      exact hinv t
  | transact w pub hN hM hC newNotes unshieldTail rest spent' records ownedRecords
      hRoot hSplit hUnshieldLen hRemove hNullify hRecords hOwnedRecords hCapacity =>
    intro t
    by_cases ht : t = w.token
    · subst ht
      simp only [if_pos]
      have hsum := removeAll_sum (fun p => p.2.value) hRemove
      have hbal := transact_balance hN hM hC hSplit
      have hinv_t := hinv w.token
      have hpos := withPositionsFrom_map CommitmentPreimage.value s.leaves.length newNotes
      simp only [List.map_append, listSum_append]
      rw [hpos]
      omega
    · simp only [if_neg ht]
      exact hinv t
  | transactOwned w pub hN hM hC caller hCaller rest spent' ownedOutputs
      hRoot hRemove hNullify hNonZero hOwnedOutputs hCapacity =>
    intro t
    by_cases ht : t = w.token
    · subst ht
      simp only [if_pos]
      have hsum := removeAll_sum (fun p => p.2.value) hRemove
      have hbal := transactOwned_balance hN hM hC
      have hinv_t := hinv w.token
      have hpos := withPositionsFrom_map CommitmentPreimage.value s.leaves.length (ownedNewNotes w)
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
are `hRoot : pub.merkleRoot ∈ s.roots`, `hRemove : removeAll (s.live w.token)
(transactSpentPositions w) = some rest` and `hNullify : markSpent s.spent (...) = some
spent'`. None of them reads `s.shieldsPaused`, the one field any step other than
`Step.shield`/`.transact`/`.transactOwned` can change (`Step.admin`, the one remaining
owner-controlled path — the module comment on `Step.transact` records the departure
this closes). So the exact witnesses that make a `transact` valid from `s` also make
the identical `transact` valid from `s` with `shieldsPaused` flipped to any `b`: an
admin step can never turn a valid spend into an invalid one. The proof is immediate
reapplication of `Step.transact`'s own constructor — the state `{ s with shieldsPaused
:= b }` agrees with `s` on `roots`, `live` and `spent` definitionally, since a
record-field update touches only the one field named. -/
theorem transact_cannot_be_blocked {s : PoolState} (b : Bool)
    {N M : Nat} (w : TransactWitness N M) (pub : TransactPublic N M)
    (hN : N ≤ 8) (hM : M ≤ 4) (hC : Constrained w pub)
    (newNotes unshieldTail : List CommitmentPreimage)
    (rest : List (Nat × CommitmentPreimage)) (spent' : NullifierSet)
    (records : List (Term × CommitmentPreimage))
    (ownedRecords : List (Term × OwnedDisclosure))
    (hRoot : pub.merkleRoot ∈ s.roots)
    (hSplit : transactAllOutputs w = newNotes ++ unshieldTail)
    (hUnshieldLen : unshieldTail.length ≤ 1)
    (hRemove : removeAll (s.live w.token) (transactSpentPositions w) = some rest)
    (hNullify : markSpent s.spent (List.ofFn pub.nullifiers) = some spent')
    (hRecords : records.Sublist (transactOutputRecords w pub))
    (hOwnedRecords : ∀ cd ∈ ownedRecords, ∃ pre, (cd.1, pre) ∈ records ∧
      npk cd.2.ownerField cd.2.random = pre.npk)
    (hCapacity : s.leaves.length + newNotes.length ≤ 2 ^ TreeDepth) :
    ∃ s', Step { s with shieldsPaused := b } s' :=
  ⟨_, Step.transact w pub hN hM hC newNotes unshieldTail rest spent' records ownedRecords
    hRoot hSplit hUnshieldLen hRemove hNullify hRecords hOwnedRecords hCapacity⟩

/-- The owned-path counterpart of `transact_cannot_be_blocked`: no step any caller can
    take, the owner included, can make an otherwise-valid `transactOwned` fail. Same
    proof shape: `Step.transactOwned`'s preconditions never read `s.shieldsPaused`
    either. -/
theorem transactOwned_cannot_be_blocked {s : PoolState} (b : Bool)
    {N M : Nat} (w : TransactOwnedWitness N M) (pub : TransactOwnedPublic N M)
    (hN : N ≤ 8) (hM : M ≤ 4) (hC : OwnedConstrained w pub)
    (caller : Term) (hCaller : caller = pub.ownerField)
    (rest : List (Nat × CommitmentPreimage)) (spent' : NullifierSet)
    (ownedOutputs : List (Fin M × OwnedDisclosure))
    (hRoot : pub.merkleRoot ∈ s.roots)
    (hRemove : removeAll (s.live w.token) (ownedSpentPositions pub w) = some rest)
    (hNullify : markSpent s.spent (List.ofFn pub.nullifiers) = some spent')
    (hNonZero : ∀ j, ¬ isZeroPreimage
      (⟨w.npkOut j, w.token, w.valueOut j⟩ : CommitmentPreimage))
    (hOwnedOutputs : ∀ x ∈ ownedOutputs, npk x.2.ownerField x.2.random = w.npkOut x.1)
    (hCapacity : s.leaves.length + M ≤ 2 ^ TreeDepth) :
    ∃ s', Step { s with shieldsPaused := b } s' :=
  ⟨_, Step.transactOwned w pub hN hM hC caller hCaller rest spent' ownedOutputs
    hRoot hRemove hNullify hNonZero hOwnedOutputs hCapacity⟩

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

/-- One step never un-spends a nullifier. -/
theorem spent_monotone {s s' : PoolState} (hstep : Step s s') : ∀ n ∈ s.spent, n ∈ s'.spent := by
  cases hstep with
  | shield token grossAmount feeBP npk hNotPaused hValue hFeeBP hCapacity =>
    exact fun n hn => hn
  | transact w pub hN hM hC newNotes unshieldTail rest spent' records ownedRecords
      hRoot hSplit hUnshieldLen hRemove hNullify hRecords hOwnedRecords hCapacity =>
    exact markSpent_subset hNullify
  | transactOwned w pub hN hM hC caller hCaller rest spent' ownedOutputs
      hRoot hRemove hNullify hNonZero hOwnedOutputs hCapacity =>
    exact markSpent_subset hNullify
  | admin shieldsPaused =>
    exact fun n hn => hn

/-- Reachability relative to a starting state, for stating "once spent, a nullifier
    stays spent for the rest of the pool's history" without re-deriving the whole
    history from genesis every time. -/
inductive ReachableFrom : PoolState → PoolState → Prop where
  | refl {s} : ReachableFrom s s
  | step {s s' s'' : PoolState} (h : ReachableFrom s s') (hstep : Step s' s'') :
      ReachableFrom s s''

/-- A nullifier spent at the start of a history stays spent throughout it. -/
theorem spent_monotone_from {s s' : PoolState} (h : ReachableFrom s s') :
    ∀ n ∈ s.spent, n ∈ s'.spent := by
  induction h with
  | refl => exact fun n hn => hn
  | step _ hstep ih => exact fun n hn => spent_monotone hstep n (ih n hn)

/--
**No double spend across transactions.** If a nullifier `n` is already spent at a
reachable state `s0`, then at any later point `s` in the same history
(`ReachableFrom s0 s`), no `transact`/`transactOwned` call can mark `n` again: `n` is not
among the nullifiers any successful `markSpent` call at `s` processes. Proved by
combining `spent_monotone_from` (`n` is still in `s.spent`, since spending never
un-marks a nullifier) with `ArmadaLean.PoolOwned.owned_no_double_spend` (a successful
`markSpent` call's nullifiers are all fresh against the *current* spent set — the same
freshness check covers `transact` and `transactOwned`, since both call
`_accumulateAndNullify`, TransactModule.sol:379-386). S-RG, "RAILGUN Core System &
Protocol": "The contract checks to make sure: ... That it hasn't seen the nullifiers
before, eliminating any double spends." -/
theorem pool_no_double_spend {s0 s : PoolState}
    (_h0 : Reachable s0) (hfrom : ReachableFrom s0 s)
    {n : Term} (hn0 : n ∈ s0.spent) {ns : List Term} {spent' : NullifierSet}
    (hmark : markSpent s.spent ns = some spent') : n ∉ ns := by
  intro hmem
  exact (owned_no_double_spend hmark).2 n hmem (spent_monotone_from hfrom n hn0)

/-! ### Two different live positions never share a nullifier -/

/--
**Two different live positions never share a nullifier.** `nullifier`'s two
arguments combine in one `Term.hash2` call
(`ArmadaLean.Nullifier.nullifier_pos_inj`), so for any one spender's key (plain
`nullifyingKey` or owned `ownerField` alike — `nullifier` does not distinguish the
two), distinct leaf positions always derive distinct nullifiers. This is the fact that
makes identifying a live note by its position sound in the first place: `PoolState
.live`'s `(position, preimage)` pairs (module comment, Pool.lean) can never be
confused by the nullifier a spend proof publishes for one of them, because no other
live position could ever produce that same nullifier under the same key. -/
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
positions they land at (`withPositionsFrom`), plus that same remainder, by
`Step.transact`/`Step.transactOwned`'s own construction (where `spentPositions` is
always `transactSpentPositions w`/`ownedSpentPositions pub w`, read off the proof's own
witness — never a free choice,
`ArmadaLean.PoolSafety.transact_spends_only_owned`/`.transactOwned_spends_only_owned`).
A spend of a position that is not live has no step: `removeAll` returns `none` the
moment a requested position is missing, so no `Step.transact`/`.transactOwned` term can
be built at all. S-RG, "How Does RAILGUN Work?": "The input notes are moved from the
live pool to the dead pool, and the output notes are added to the live pool." (Armada
keeps no separate dead pool — a spent note stays in the Merkle tree, only its
nullifier is marked — so "moved to the dead pool" corresponds here to "removed from
`live`", the model's own live-note bookkeeping.) -/
theorem spend_live_exact {s : PoolState} {token : Nat}
    {spentPositions : List (Nat × CommitmentPreimage)} {newNotes : List CommitmentPreimage}
    {rest : List (Nat × CommitmentPreimage)}
    (hRemove : removeAll (s.live token) spentPositions = some rest) :
    (s.live token).Perm (spentPositions ++ rest) ∧
      ({ s with
          live := fun t => if t = token
              then withPositionsFrom s.leaves.length newNotes ++ rest else s.live t } :
        PoolState).live token = withPositionsFrom s.leaves.length newNotes ++ rest :=
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
**A shield creates exactly one note of the shielded amount minus the fee, at leaf
position `s.leaves.length`.** By `Step.shield`'s construction: the live set of the
shielded token gains exactly the one `(position, preimage)` entry
`(s.leaves.length, ⟨npk, token, shieldBase feeBP grossAmount⟩)` — the position the
caller can record as where its new note sits; the pool's custody of that token rises
by exactly that note's value; neither changes for any other token; no second ("fee")
note is created (see the module comment on the departure from the brief's design and
from the design labbook). S-RG, "RAILGUN Core System & Protocol": "Then the smart
contract transfers tokens from the user wallet to itself, if a deposit amount is
specified ... The hashes of the output UTXOs are then added to the Merkle tree." -/
theorem shield_creates_exactly {s : PoolState} (token grossAmount feeBP : Nat) (npk : Term)
    (hNotPaused : s.shieldsPaused = false) (hValue : 0 < grossAmount)
    (hFeeBP : feeBP ≤ BASIS) (hCapacity : s.leaves.length + 1 ≤ 2 ^ TreeDepth) :
    ∃ s', Step s s' ∧
      s'.live token =
        (s.leaves.length,
          (⟨npk, token, shieldBase feeBP grossAmount⟩ : CommitmentPreimage)) :: s.live token ∧
      s'.held token = s.held token + shieldBase feeBP grossAmount ∧
      (∀ t, t ≠ token → s'.live t = s.live t ∧ s'.held t = s.held t) :=
  ⟨_, Step.shield token grossAmount feeBP npk hNotPaused hValue hFeeBP hCapacity,
    by simp, by simp, fun t ht => ⟨by simp [ht], by simp [ht]⟩⟩

/-! ### A transact names only a root the pool actually produced -/

/-- One step either leaves `roots` unchanged (`Step.admin`) or prepends exactly one new
    root (`shield`/`transact`/`transactOwned`) — the structural fact `roots_grounded`
    needs, stated without naming the pushed root's value, since each constructor
    computes a different one from `ArmadaLean.Merkle.treeRoot`. -/
theorem step_roots_shape {s s' : PoolState} (hstep : Step s s') :
    s'.roots = s.roots ∨ ∃ r, s'.roots = r :: s.roots := by
  cases hstep with
  | shield token grossAmount feeBP npk hNotPaused hValue hFeeBP hCapacity =>
    exact Or.inr ⟨_, rfl⟩
  | transact w pub hN hM hC newNotes unshieldTail rest spent' records ownedRecords
      hRoot hSplit hUnshieldLen hRemove hNullify hRecords hOwnedRecords hCapacity =>
    exact Or.inr ⟨_, rfl⟩
  | transactOwned w pub hN hM hC caller hCaller rest spent' ownedOutputs
      hRoot hRemove hNullify hNonZero hOwnedOutputs hCapacity =>
    exact Or.inr ⟨_, rfl⟩
  | admin shieldsPaused =>
    exact Or.inl rfl

/-- Every reachable state's root history is `genesis.roots` with zero or more roots the
    pool itself pushed, prepended. -/
theorem roots_grounded {s : PoolState} (h : Reachable s) :
    ∃ pushed : List Term, s.roots = pushed ++ genesis.roots := by
  induction h with
  | genesis => exact ⟨[], rfl⟩
  | step _ hstep ih =>
    obtain ⟨pushed, hpushed⟩ := ih
    rcases step_roots_shape hstep with heq | ⟨r, heq⟩
    · exact ⟨pushed, heq.trans hpushed⟩
    · exact ⟨r :: pushed, by rw [heq, hpushed, List.cons_append]⟩

/--
**A transact names only a root the pool actually produced.** `roots_grounded` shows
`s.roots`, for any reachable `s`, is built from `genesis.roots` by prepending values the
pool itself pushed at earlier `shield`/`transact`/`transactOwned` steps — never anything
else. A `transact`/`transactOwned`/`shield` step's own `hRoot : pub.merkleRoot ∈ s.roots`
precondition then means the named root is one of those pushed values, or the genesis
root — never a caller's invention. S-RG, "RAILGUN Core System & Protocol": "The contract
checks to make sure: ... The Merkle root is the current or a previous Merkle root, to
prevent users from making up UTXOs." -/
theorem transact_root_was_produced {s : PoolState}
    (h : Reachable s) {root : Term} (hRoot : root ∈ s.roots) :
    root ∈ genesis.roots ∨
      ∃ pushed : List Term, root ∈ pushed ∧ s.roots = pushed ++ genesis.roots := by
  obtain ⟨pushed, hpushed⟩ := roots_grounded h
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
    | shield token grossAmount feeBP npk hNotPaused hValue hFeeBP hCapacity =>
      exact recordStep_preserves_consistency ih rfl
    | transact w pub hN hM hC newNotes unshieldTail rest spent' records ownedRecords
        hRoot hSplit hUnshieldLen hRemove hNullify hRecords hOwnedRecords hCapacity =>
      exact applyRecords_preserves_consistency ih
        (fun cp hcp => transactOutputRecords_valid hC cp (hRecords.subset hcp))
    | transactOwned w pub hN hM hC caller hCaller rest spent' ownedOutputs
        hRoot hRemove hNullify hNonZero hOwnedOutputs hCapacity =>
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
    | shield token grossAmount feeBP npk hNotPaused hValue hFeeBP hCapacity =>
      intro c d hc
      obtain ⟨pre, hreg, hnpk⟩ := ih c d hc
      exact ⟨pre, recordStep_preserves_other (pool_preimageOf_consistent hs c pre hreg) hreg rfl,
        hnpk⟩
    | transact w pub hN hM hC newNotes unshieldTail rest spent' records ownedRecords
        hRoot hSplit hUnshieldLen hRemove hNullify hRecords hOwnedRecords hCapacity =>
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
    | transactOwned w pub hN hM hC caller hCaller rest spent' ownedOutputs
        hRoot hRemove hNullify hNonZero hOwnedOutputs hCapacity =>
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
    honest-prover assumption: shield carries no SNARK. -/
theorem shield_can_happen {s : PoolState} (token grossAmount feeBP : Nat) (npk : Term)
    (hNotPaused : s.shieldsPaused = false) (hValue : 0 < grossAmount)
    (hFeeBP : feeBP ≤ BASIS) (hCapacity : s.leaves.length + 1 ≤ 2 ^ TreeDepth) :
    ∃ s', Step s s' :=
  ⟨_, Step.shield token grossAmount feeBP npk hNotPaused hValue hFeeBP hCapacity⟩

/-- **Can happen: a transact (private transfer, no unshield) succeeds.** A real key
    holder with `N` genuinely-held, genuinely-live notes, re-minting them into `M` fresh
    notes of equal total value, clears every gate `Step.transact` checks: the witness is
    built and shown `Constrained` exactly as `transact_spend_can_happen` builds one
    (inlined here, not obtained from that theorem's existential, so `w`'s fields stay
    definitionally the caller's own data — `Step.transact`'s `hRemove`/`hSplit`
    hypotheses need that transparency), `hComplete.complete` shows `verify` accepts, and
    `markSpent_succeeds` (with `distinct_leaves_distinct_nullifiers`) shows the
    nullifiers are fresh. `hLive` is the ghost liveness precondition, keyed by the exact
    leaf positions the holder's notes sit at (the model's own record of what it minted
    for them earlier, and where); `hN`/`hM` the registered-shape bound. `records := []`,
    `ownedRecords := []`: a plain transact's `publicOutputs` is optional
    (TransactModule.sol:556-561), so no contract-owned output is needed here. -/
theorem transact_can_happen {s : PoolState} (hComplete : TransactProofCompleteness)
    (hSig : HonestSignature) {N M : Nat} (publicKey : Nat × Nat)
    (nullifyingKey token boundParamsHash : Nat) (root : Term)
    (randomIn valueIn : Fin N → Nat) (leavesIndices : Fin N → Nat)
    (pathElements : Fin N → List (Term × Bool)) (npkOut : Fin M → Term) (valueOut : Fin M → Nat)
    (hN : N ≤ 8) (hM : M ≤ 4)
    (hRoot : root ∈ s.roots)
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
    (hFresh : ∀ i, nullifier (Term.val nullifyingKey) (leavesIndices i) ∉ s.spent)
    {rest : List (Nat × CommitmentPreimage)}
    (hLive : removeAll (s.live token)
        (List.ofFn fun i =>
          (leavesIndices i,
            (⟨npk (masterPublicKey publicKey nullifyingKey) (randomIn i), token, valueIn i⟩ :
              CommitmentPreimage)))
        = some rest)
    (hCapacity : s.leaves.length + M ≤ 2 ^ TreeDepth) :
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
    (show ∀ n ∈ List.ofFn (fun i => nullifier (Term.val nullifyingKey) (leavesIndices i)), n ∉ s.spent by
      intro n hn
      obtain ⟨i, hi⟩ := List.mem_ofFn.mp hn
      rw [← hi]
      exact hFresh i)
  refine ⟨_, Step.transact w pub hN hM hC
    (List.ofFn fun j => (⟨npkOut j, token, valueOut j⟩ : CommitmentPreimage)) [] rest spent'
    [] [] hRoot (by simp [transactAllOutputs, w])
    (by simp) hLive hMark (List.nil_sublist _) (by simp) (by rwa [List.length_ofFn])⟩

/-- **Can happen: an unshield succeeds.** The degenerate single-output shape of
    `transact_can_happen`: a real key holder spends `N` genuinely-held, genuinely-live
    notes and the circuit's one output is the unshield payout itself (`newNotes := []`,
    the entire spent value becomes the unshield payout) — `_validateTransaction`'s
    unshield checks (TransactModule.sol:295-331; see the Zokyo 2022-12-21 finding #1
    cited at `Step.transact`) are exactly what licenses reading the circuit's one output
    as the payout amount. -/
theorem unshield_can_happen {s : PoolState} (hComplete : TransactProofCompleteness)
    (hSig : HonestSignature) {N : Nat} (publicKey : Nat × Nat)
    (nullifyingKey token boundParamsHash : Nat) (root : Term)
    (randomIn valueIn : Fin N → Nat) (leavesIndices : Fin N → Nat)
    (pathElements : Fin N → List (Term × Bool)) (npkOut : Term) (valueOut : Nat)
    (hN : N ≤ 8)
    (hRoot : root ∈ s.roots)
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
    (hFresh : ∀ i, nullifier (Term.val nullifyingKey) (leavesIndices i) ∉ s.spent)
    {rest : List (Nat × CommitmentPreimage)}
    (hLive : removeAll (s.live token)
        (List.ofFn fun i =>
          (leavesIndices i,
            (⟨npk (masterPublicKey publicKey nullifyingKey) (randomIn i), token, valueIn i⟩ :
              CommitmentPreimage)))
        = some rest)
    (hCapacity : s.leaves.length ≤ 2 ^ TreeDepth) :
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
    (show ∀ n ∈ List.ofFn (fun i => nullifier (Term.val nullifyingKey) (leavesIndices i)), n ∉ s.spent by
      intro n hn
      obtain ⟨i, hi⟩ := List.mem_ofFn.mp hn
      rw [← hi]
      exact hFresh i)
  refine ⟨_, Step.transact w pub hN (by omega) hC []
    (List.ofFn fun (_ : Fin 1) => (⟨npkOut, token, valueOut⟩ : CommitmentPreimage)) rest
    spent' [] [] hRoot
    (by simp [transactAllOutputs, w]) (by simp) hLive hMark (List.nil_sublist _) (by simp)
    (by simpa)⟩

/-- **Can happen: an owned transact succeeds.** Directly wires an owned witness,
    constructed exactly as `ArmadaLean.PoolOwned.owned_spend_can_happen` builds one
    (inlined here, not obtained from that theorem's existential, for the same
    definitional-transparency reason as `transact_can_happen`), into
    `Step.transactOwned`: `hLive` supplies the ghost liveness precondition, keyed by
    the exact leaf positions the owner's notes sit at (the model's own record of what
    it minted for them, and where), `hN`/`hM` the registered-shape bound,
    `caller`/`hCaller` the authorization check
    (`ArmadaLean.PoolSafety.transactOwned_spends_only_owned` is the matching safety
    theorem). An owned transact can pay out to any recipient's own note key, not only
    re-mint notes to itself (module comment, `Step.transactOwned`), so this witness
    supplies no owned-random disclosure for the new outputs (`ownedOutputs := []`) —
    a disclosed, contract-owned output is a separate, later act
    (`ArmadaLean.PoolOwned`'s module comment on `OwnedDisclosure`), not a precondition
    for the spend itself to succeed. -/
theorem owned_transact_can_happen {s : PoolState} (hComplete : OwnedProofCompleteness)
    {N M : Nat} (ownerField : Term) (token boundParamsHash : Nat) (root : Term)
    (randomIn valueIn : Fin N → Nat) (leavesIndices : Fin N → Nat)
    (pathElements : Fin N → List (Term × Bool)) (npkOut : Fin M → Term) (valueOut : Fin M → Nat)
    (hN : N ≤ 8) (hM : M ≤ 4)
    (hRoot : root ∈ s.roots)
    (hPathLen : ∀ i, (pathElements i).length = 16)
    (hMerkle : ∀ i,
      merkleRoot (commitment (npk ownerField (randomIn i)) token (valueIn i))
        (pathElements i) = root)
    (hRangeIn : ∀ i, RangeChecked120 (valueIn i))
    (hRangeOut : ∀ j, RangeChecked120 (valueOut j))
    (hBalance : listSum (List.ofFn valueIn) = listSum (List.ofFn valueOut))
    (hDistinctLeaves : (List.ofFn leavesIndices).Pairwise (· ≠ ·))
    (hFresh : ∀ i, nullifier ownerField (leavesIndices i) ∉ s.spent)
    (hOutputsNonZero : ∀ j, npkOut j ≠ Term.val 0)
    (caller : Term) (hCaller : caller = ownerField)
    {rest : List (Nat × CommitmentPreimage)}
    (hLive : removeAll (s.live token)
        (List.ofFn fun i =>
          (leavesIndices i,
            (⟨npk ownerField (randomIn i), token, valueIn i⟩ : CommitmentPreimage)))
        = some rest)
    (hCapacity : s.leaves.length + M ≤ 2 ^ TreeDepth) :
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
    (show ∀ n ∈ List.ofFn (fun i => nullifier ownerField (leavesIndices i)), n ∉ s.spent by
      intro n hn
      obtain ⟨i, hi⟩ := List.mem_ofFn.mp hn
      rw [← hi]
      exact hFresh i)
  refine ⟨_, Step.transactOwned w pub hN hM hC caller hCaller rest spent' []
    hRoot hLive hMark ?_ (fun x hx => absurd hx (List.not_mem_nil)) hCapacity⟩
  intro j hz
  exact hOutputsNonZero j hz.1

/-! ### Every inserted leaf has a Merkle witness to a root the pool produced -/

/-- One step either leaves `leaves`/`roots` both unchanged (`Step.admin`) or appends to
    `leaves` and pushes exactly `ArmadaLean.Merkle.treeRoot TreeDepth` of the new list
    (`shield`/`transact`/`transactOwned`) — the structural fact
    `reachable_root_matches_leaves` and `reachable_leaves_capacity` both need, stated
    without naming the appended leaves, since each constructor appends a different
    list. -/
theorem step_leaves_root_shape {s s' : PoolState} (hstep : Step s s') :
    (s'.leaves = s.leaves ∧ s'.roots = s.roots) ∨
      s'.roots = treeRoot TreeDepth s'.leaves :: s.roots := by
  cases hstep with
  | shield token grossAmount feeBP npk hNotPaused hValue hFeeBP hCapacity =>
    exact Or.inr rfl
  | transact w pub hN hM hC newNotes unshieldTail rest spent' records ownedRecords
      hRoot hSplit hUnshieldLen hRemove hNullify hRecords hOwnedRecords hCapacity =>
    exact Or.inr rfl
  | transactOwned w pub hN hM hC caller hCaller rest spent' ownedOutputs
      hRoot hRemove hNullify hNonZero hOwnedOutputs hCapacity =>
    exact Or.inr rfl
  | admin shieldsPaused =>
    exact Or.inl ⟨rfl, rfl⟩

/-- **The root the pool most recently pushed always matches its actual leaf list.**
    Every reachable state's head root is `ArmadaLean.Merkle.treeRoot TreeDepth` of its
    own `leaves` — never a free choice (`Step`'s construction, `step_leaves_root_shape`),
    proved by induction on `Reachable`. -/
theorem reachable_root_matches_leaves {s : PoolState} (h : Reachable s) :
    treeRoot TreeDepth s.leaves ∈ s.roots := by
  induction h with
  | genesis => simp [genesis]
  | step hs hstep ih =>
    rcases step_leaves_root_shape hstep with ⟨hleaves, hroots⟩ | hroots
    · rw [hleaves, hroots]; exact ih
    · rw [hroots]; exact List.mem_cons_self

/-- **The pool's leaf list never exceeds the one tree's capacity.** Every reachable
    state's `leaves` has at most `2 ^ TreeDepth` entries — the invariant each `Step`
    constructor's own `hCapacity` hypothesis maintains (the one-tree-only departure,
    `ArmadaLean.Merkle`'s module comment): a step that would overflow the tree simply
    has no witness. -/
theorem reachable_leaves_capacity {s : PoolState} (h : Reachable s) :
    s.leaves.length ≤ 2 ^ TreeDepth := by
  induction h with
  | genesis => simp [genesis]
  | step hs hstep ih =>
    cases hstep with
    | shield token grossAmount feeBP npk hNotPaused hValue hFeeBP hCapacity =>
      simpa using hCapacity
    | transact w pub hN hM hC newNotes unshieldTail rest spent' records ownedRecords
        hRoot hSplit hUnshieldLen hRemove hNullify hRecords hOwnedRecords hCapacity =>
      simpa using hCapacity
    | transactOwned w pub hN hM hC caller hCaller rest spent' ownedOutputs
        hRoot hRemove hNullify hNonZero hOwnedOutputs hCapacity =>
      simpa [ownedNewNotes] using hCapacity
    | admin shieldsPaused =>
      simpa using ih

/--
**Every leaf the pool has ever inserted has a real Merkle witness to a root the pool
produced.** For any reachable state `s` and any in-range leaf position `i`, the path
`ArmadaLean.Merkle.treePath TreeDepth s.leaves i` is a genuine membership proof: folding
it from the leaf at position `i` reconstructs `treeRoot TreeDepth s.leaves`
(`treePath_correct`, `reachable_leaves_capacity` for the depth bound), and that root is
itself one of the pool's own, `s.roots` (`reachable_root_matches_leaves`) — the current
root, in the sense of "the one current when the leaf was inserted, or a later one",
since `roots` never expires an entry (`PrivacyPoolStorage.rootHistory`,
PrivacyPoolStorage.sol:171) and every later step only ever prepends to it
(`step_roots_shape`): the witness built from the LATEST leaf list and root always
verifies against a root the contract still accepts, for every leaf inserted so far,
not only the ones inserted in the step that produced that exact root. -/
theorem leaf_has_merkle_witness {s : PoolState} (h : Reachable s)
    {i : Nat} (hi : i < s.leaves.length) :
    merkleRoot (s.leaves.getD i (Term.val 0)) (treePath TreeDepth s.leaves i) =
        treeRoot TreeDepth s.leaves ∧
      treeRoot TreeDepth s.leaves ∈ s.roots := by
  have hcap := reachable_leaves_capacity h
  exact ⟨treePath_correct TreeDepth s.leaves i (by omega), reachable_root_matches_leaves h⟩

/-! ### A live owned note with a recorded preimage has a constructible spend witness -/

/--
**A live owned note with a recorded preimage has a constructible `OwnedConstrained`
spend witness, built entirely from public data.** Given `N` input notes whose recorded
preimages (`preimages`, exactly what `PoolState.preimageOf` records for every
disclosed output — public: every entry there came from a `shield`/`transact`
/`transactOwned` event, PrivacyPoolStorage.preimageOf, PrivacyPoolStorage.sol:248) sit
at known leaf positions in the pool's actual leaf list (`hLeafValue`, public: every
leaf is a commitment the pool has itself emitted), and each is on record as a
contract-owned note belonging to `ownerField` in the public `ownedRandomOf` registry
(`hOwned`, `ArmadaLean.PoolOwned`'s module comment on `OwnedDisclosure` — the approved
design this models), a satisfying `OwnedConstrained` witness/public pair exists — its
Merkle path is `ArmadaLean.Merkle.treePath TreeDepth leaves`, computed, not a free
choice, and `treePath_correct` is exactly what proves it satisfies `OwnedConstrained
.merkle`.

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
      (∀ i, w.valueIn i = (preimages i).value) := by
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
  exact ⟨w, pub, hC, rfl, rfl, rfl, fun _ => rfl⟩
