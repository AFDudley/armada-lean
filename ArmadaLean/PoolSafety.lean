/-
  ArmadaLean.PoolSafety — the pool contract's safety theorems, over ArmadaLean.Pool.
-/
import ArmadaLean.Pool

/-! ### The core invariant: tokens held equal the value of unspent notes -/

/-- The core invariant: for each token, the tokens the pool holds equal the total value
    of its unspent notes. -/
def HeldInvariant (s : PoolState) : Prop :=
  ∀ t, s.held t = listSum ((s.live t).map CommitmentPreimage.value)

theorem genesis_invariant (emptyRoot : Nat) : HeldInvariant (genesis emptyRoot) := by
  intro t
  simp [genesis, listSum]

/-- The value projection of a `List.ofFn`-built list of notes, all sharing one `token`
    and one key-derivation `mk`, is exactly the underlying value function. Bridges the
    circuit's `Fin`-indexed `valueIn`/`valueOut` and the pool's `List`-indexed note
    bookkeeping everywhere below. -/
theorem value_ofFn_eq {N : Nat} (mk g : Fin N → Nat) (token : Nat) :
    (List.ofFn (fun i => (⟨mk i, token, g i⟩ : CommitmentPreimage))).map
        CommitmentPreimage.value = List.ofFn g := by
  rw [List.map_ofFn]
  rfl

/-- **The balance a `Step.transact` moves is derived, not assumed.** `transactSpentNotes`
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
    listSum ((transactSpentNotes w).map CommitmentPreimage.value) =
      listSum (newNotes.map CommitmentPreimage.value) +
        listSum (unshieldTail.map CommitmentPreimage.value) := by
  have hbal := transact_value_conserved w pub hN hM hC
  have hSplit' := congrArg (List.map CommitmentPreimage.value) hSplit
  rw [List.map_append] at hSplit'
  unfold transactAllOutputs at hSplit'
  rw [value_ofFn_eq] at hSplit'
  unfold transactSpentNotes
  rw [value_ofFn_eq, hbal, hSplit', listSum_append]

/-- The owned-path counterpart of `transact_balance`: no unshield split, since
    `transactOwned` never unshields. -/
theorem transactOwned_balance {N M : Nat} {w : TransactOwnedWitness N M}
    {pub : TransactOwnedPublic N M} (hN : N ≤ 8) (hM : M ≤ 4) (hC : OwnedConstrained w pub) :
    listSum ((ownedSpentNotes pub w).map CommitmentPreimage.value) =
      listSum ((ownedNewNotes w).map CommitmentPreimage.value) := by
  have hbal := transactOwned_value_conserved w pub hN hM hC
  unfold ownedSpentNotes ownedNewNotes
  rw [value_ofFn_eq, value_ofFn_eq]
  exact hbal

theorem step_preserves_invariant {s s' : PoolState} (hinv : HeldInvariant s)
    (hstep : Step s s') : HeldInvariant s' := by
  cases hstep with
  | shield token npk grossAmount feeBP newRoot hNotPaused hValue hFeeBP =>
    intro t
    by_cases ht : t = token
    · simp only [ht, if_pos]
      have hinv_t := hinv token
      simp only [List.map_cons, listSum]
      omega
    · simp only [if_neg ht]
      exact hinv t
  | transact w pub hN hM hC newNotes unshieldTail rest spent' newRoot records
      hEmergency hWithdrawOnly hRoot hSplit hUnshieldLen hRemove hNullify hValid =>
    intro t
    by_cases ht : t = w.token
    · subst ht
      simp only [if_pos]
      have hsum := removeAll_sum hRemove
      have hbal := transact_balance hN hM hC hSplit
      have hinv_t := hinv w.token
      simp only [List.map_append, listSum_append]
      omega
    · simp only [if_neg ht]
      exact hinv t
  | transactOwned w pub hN hM hC caller hCaller rest spent' newRoot records
      hEmergency hWithdrawOnly hRoot hRemove hNullify hValid =>
    intro t
    by_cases ht : t = w.token
    · subst ht
      simp only [if_pos]
      have hsum := removeAll_sum hRemove
      have hbal := transactOwned_balance hN hM hC
      have hinv_t := hinv w.token
      simp only [List.map_append, listSum_append]
      omega
    · simp only [if_neg ht]
      exact hinv t
  | admin shieldsPaused emergencyPaused withdrawOnlyMode =>
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
theorem core_invariant {emptyRoot : Nat} {s : PoolState} (h : Reachable emptyRoot s) :
    HeldInvariant s := by
  induction h with
  | genesis => exact genesis_invariant emptyRoot
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
    {trueMpk trueRandom : Nat}
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
    {trueOwner trueRandom : Nat}
    (hSameNote :
      commitment (npk pub.ownerField (w.randomIn i)) w.token (w.valueIn i) =
      commitment (npk trueOwner trueRandom) w.token (w.valueIn i))
    {caller : Nat} (hCaller : caller = addressOf pub.ownerField) :
    caller = addressOf trueOwner :=
  owned_owner_binding hC i hSameNote hCaller

/-! ### No double spend across transactions -/

/-- A successful `markSpent` call never drops a nullifier that was already marked: it
    only ever grows the set (`markSpent`'s recursive case prepends, it never removes). -/
theorem markSpent_subset {spent spent' : NullifierSet} {ns : List Nat}
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
  | shield token npk grossAmount feeBP newRoot hNotPaused hValue hFeeBP =>
    exact fun n hn => hn
  | transact w pub hN hM hC newNotes unshieldTail rest spent' newRoot records
      hEmergency hWithdrawOnly hRoot hSplit hUnshieldLen hRemove hNullify hValid =>
    exact markSpent_subset hNullify
  | transactOwned w pub hN hM hC caller hCaller rest spent' newRoot records
      hEmergency hWithdrawOnly hRoot hRemove hNullify hValid =>
    exact markSpent_subset hNullify
  | admin shieldsPaused emergencyPaused withdrawOnlyMode =>
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
theorem pool_no_double_spend {emptyRoot : Nat} {s0 s : PoolState}
    (_h0 : Reachable emptyRoot s0) (hfrom : ReachableFrom s0 s)
    {n : Nat} (hn0 : n ∈ s0.spent) {ns : List Nat} {spent' : NullifierSet}
    (hmark : markSpent s.spent ns = some spent') : n ∉ ns := by
  intro hmem
  exact (owned_no_double_spend hmark).2 n hmem (spent_monotone_from hfrom n hn0)

/-! ### A spend removes exactly what it spends, and adds exactly its new notes -/

/--
**A spend removes exactly the notes it spends from the live set, and adds exactly its
new notes.** Before the step, the live notes of the spent token are exactly the spent
notes plus a remainder (`removeAll_perm`, a multiset statement: a note's commitment
need not be unique, so "exactly" means multiset equality, not set equality). After the
step, the live notes of that token are exactly the new notes plus that same remainder,
by `Step.transact`/`Step.transactOwned`'s own construction (where `spentNotes` is always
`transactSpentNotes w`/`ownedSpentNotes pub w`, read off the proof's own witness — never a
free choice, `ArmadaLean.PoolSafety.transact_spends_only_owned`/
`.transactOwned_spends_only_owned`). S-RG, "How Does RAILGUN Work?": "The input notes are
moved from the live pool to the dead pool, and the output notes are added to the live
pool." (Armada keeps no separate dead pool — a spent note stays in the Merkle tree, only
its nullifier is marked — so "moved to the dead pool" corresponds here to "removed from
`live`", the model's own live-note bookkeeping.) -/
theorem spend_live_exact {s : PoolState} {token : Nat}
    {spentNotes newNotes rest : List CommitmentPreimage}
    (hRemove : removeAll (s.live token) spentNotes = some rest) :
    (s.live token).Perm (spentNotes ++ rest) ∧
      ({ s with
          live := fun t => if t = token then newNotes ++ rest else s.live t } :
        PoolState).live token = newNotes ++ rest :=
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
**A shield creates exactly one note of the shielded amount minus the fee.** By
`Step.shield`'s construction: the live set of the shielded token gains exactly the one
note `⟨npk, token, shieldBase feeBP grossAmount⟩`; the pool's custody of that token rises
by exactly that note's value; neither changes for any other token; no second ("fee")
note is created (see the module comment on the departure from the brief's design and
from the design labbook). S-RG, "RAILGUN Core System & Protocol": "Then the smart
contract transfers tokens from the user wallet to itself, if a deposit amount is
specified ... The hashes of the output UTXOs are then added to the Merkle tree." -/
theorem shield_creates_exactly {s : PoolState} (token npk grossAmount feeBP newRoot : Nat)
    (hNotPaused : s.shieldsPaused = false) (hValue : 0 < grossAmount)
    (hFeeBP : feeBP ≤ BASIS) :
    ∃ s', Step s s' ∧
      s'.live token =
        (⟨npk, token, shieldBase feeBP grossAmount⟩ : CommitmentPreimage) :: s.live token ∧
      s'.held token = s.held token + shieldBase feeBP grossAmount ∧
      (∀ t, t ≠ token → s'.live t = s.live t ∧ s'.held t = s.held t) :=
  ⟨_, Step.shield token npk grossAmount feeBP newRoot hNotPaused hValue hFeeBP,
    by simp, by simp, fun t ht => ⟨by simp [ht], by simp [ht]⟩⟩

/-! ### A transact names only a root the pool actually produced -/

/-- Every reachable state's root history is the genesis root with zero or more roots the
    pool itself pushed, prepended. -/
theorem roots_grounded {emptyRoot : Nat} {s : PoolState} (h : Reachable emptyRoot s) :
    ∃ pushed : List Nat, s.roots = pushed ++ [emptyRoot] := by
  induction h with
  | genesis => exact ⟨[], by simp [genesis]⟩
  | step _ hstep ih =>
    obtain ⟨pushed, hpushed⟩ := ih
    cases hstep with
    | shield token npk grossAmount feeBP newRoot hNotPaused hValue hFeeBP =>
      exact ⟨newRoot :: pushed, by simp [hpushed]⟩
    | transact w pub hN hM hC newNotes unshieldTail rest spent' newRoot records
        hEmergency hWithdrawOnly hRoot hSplit hUnshieldLen hRemove hNullify hValid =>
      exact ⟨newRoot :: pushed, by simp [hpushed]⟩
    | transactOwned w pub hN hM hC caller hCaller rest spent' newRoot records
        hEmergency hWithdrawOnly hRoot hRemove hNullify hValid =>
      exact ⟨newRoot :: pushed, by simp [hpushed]⟩
    | admin shieldsPaused emergencyPaused withdrawOnlyMode =>
      exact ⟨pushed, hpushed⟩

/--
**A transact names only a root the pool actually produced.** `roots_grounded` shows
`s.roots`, for any reachable `s`, is built from the genesis root by prepending values the
pool itself pushed at earlier `shield`/`transact`/`transactOwned` steps — never anything
else. A `transact`/`transactOwned`/`shield` step's own `hRoot : pub.merkleRoot ∈ s.roots`
precondition then means the named root is one of those pushed values, or the genesis
root — never a caller's invention. S-RG, "RAILGUN Core System & Protocol": "The contract
checks to make sure: ... The Merkle root is the current or a previous Merkle root, to
prevent users from making up UTXOs." -/
theorem transact_root_was_produced {emptyRoot : Nat} {s : PoolState}
    (h : Reachable emptyRoot s) {root : Nat} (hRoot : root ∈ s.roots) :
    root = emptyRoot ∨ ∃ pushed : List Nat, root ∈ pushed ∧ s.roots = pushed ++ [emptyRoot] := by
  obtain ⟨pushed, hpushed⟩ := roots_grounded h
  rw [hpushed] at hRoot
  rcases List.mem_append.mp hRoot with h1 | h2
  · exact Or.inr ⟨pushed, h1, hpushed⟩
  · exact Or.inl (by simpa using h2)

/-! ### The preimage registry -/

/--
**The preimage registry is always consistent.** Every entry the pool has ever written to
`preimageOf`, at any reachable state, hashes to the commitment it is recorded under —
lifting `ArmadaLean.PoolOwned.preimageOf_consistent` from one transaction's batch
(`recordPreimages`) to the pool's whole history (`applyRecords`, at every
`shield`/`transact`/`transactOwned` step). -/
theorem pool_preimageOf_consistent {emptyRoot : Nat} {s : PoolState}
    (h : Reachable emptyRoot s) : RegistryConsistent s.preimageOf := by
  induction h with
  | genesis => intro c pre hc; simp [genesis] at hc
  | step _ hstep ih =>
    cases hstep with
    | shield token npk grossAmount feeBP newRoot hNotPaused hValue hFeeBP =>
      exact recordStep_preserves_consistency ih rfl
    | transact w pub hN hM hC newNotes unshieldTail rest spent' newRoot records
        hEmergency hWithdrawOnly hRoot hSplit hUnshieldLen hRemove hNullify hValid =>
      exact applyRecords_preserves_consistency ih hValid
    | transactOwned w pub hN hM hC caller hCaller rest spent' newRoot records
        hEmergency hWithdrawOnly hRoot hRemove hNullify hValid =>
      exact applyRecords_preserves_consistency ih hValid
    | admin shieldsPaused emergencyPaused withdrawOnlyMode =>
      exact ih

/-! ### Can happen -/

/-- Converting a `Fin`-indexed pairwise-distinctness fact (as `ArmadaLean.PoolOwned
    .owned_spend_can_happen` takes it, via `List.ofFn`) into the pointwise form
    `Constrained.distinct` needs. -/
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
    asserts the forward (signing) direction a real key holder has. -/
structure HonestSignature where
  sign : (Nat × Nat) → Nat → (Nat × Nat × Nat)
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
    (nullifyingKey token boundParamsHash root : Nat)
    (randomIn valueIn : Fin N → Nat) (leavesIndices : Fin N → Nat)
    (pathElements : Fin N → List (Nat × Bool)) (npkOut valueOut : Fin M → Nat)
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
    (hFresh : ∀ i, nullifier nullifyingKey (leavesIndices i) ∉ spent) :
    ∃ (w : TransactWitness N M) (pub : TransactPublic N M),
      Constrained w pub ∧
      VerifyAccepts pub ∧
      (∀ j, hashCommitment ⟨npkOut j, token, valueOut j⟩ = pub.commitmentsOut j) ∧
      ∃ spent', markSpent spent (List.ofFn pub.nullifiers) = some spent' := by
  let pub : TransactPublic N M :=
    { merkleRoot := root, boundParamsHash := boundParamsHash,
      nullifiers := fun i => nullifier nullifyingKey (leavesIndices i),
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
  · have hmap := distinct_leaves_distinct_nullifiers nullifyingKey (List.ofFn leavesIndices)
      hDistinctLeaves
    have heq : (List.ofFn leavesIndices).map (nullifier nullifyingKey)
        = List.ofFn (fun i => nullifier nullifyingKey (leavesIndices i)) := List.map_ofFn
    rwa [heq] at hmap
  · intro n hn
    obtain ⟨i, hi⟩ := List.mem_ofFn.mp hn
    rw [← hi]
    exact hFresh i

/-- **Can happen: a shield succeeds.** Any positive amount, at any fee rate up to 100%,
    while shields are not paused, creates a note (`shield_creates_exactly`). No proof, no
    honest-prover assumption: shield carries no SNARK. -/
theorem shield_can_happen {s : PoolState} (token npk grossAmount feeBP newRoot : Nat)
    (hNotPaused : s.shieldsPaused = false) (hValue : 0 < grossAmount)
    (hFeeBP : feeBP ≤ BASIS) : ∃ s', Step s s' :=
  ⟨_, Step.shield token npk grossAmount feeBP newRoot hNotPaused hValue hFeeBP⟩

/-- **Can happen: a transact (private transfer, no unshield) succeeds.** A real key
    holder with `N` genuinely-held, genuinely-live notes, re-minting them into `M` fresh
    notes of equal total value, clears every gate `Step.transact` checks: the witness is
    built and shown `Constrained` exactly as `transact_spend_can_happen` builds one
    (inlined here, not obtained from that theorem's existential, so `w`'s fields stay
    definitionally the caller's own data — `Step.transact`'s `hRemove`/`hSplit`
    hypotheses need that transparency), `hComplete.complete` shows `verify` accepts, and
    `markSpent_succeeds` (with `distinct_leaves_distinct_nullifiers`) shows the
    nullifiers are fresh. `hLive` is the ghost liveness precondition (the holder's notes
    are the model's own record of what it minted for them earlier); `hN`/`hM` the
    registered-shape bound. `records := []`: a plain transact's `publicOutputs` is
    optional (TransactModule.sol:556-561), so no contract-owned output is needed here. -/
theorem transact_can_happen {s : PoolState} (hComplete : TransactProofCompleteness)
    (hSig : HonestSignature) {N M : Nat} (publicKey : Nat × Nat)
    (nullifyingKey token boundParamsHash root newRoot : Nat)
    (randomIn valueIn : Fin N → Nat) (leavesIndices : Fin N → Nat)
    (pathElements : Fin N → List (Nat × Bool)) (npkOut valueOut : Fin M → Nat)
    (hN : N ≤ 8) (hM : M ≤ 4)
    (hEmergency : s.emergencyPaused = false) (hNotWithdrawOnly : s.withdrawOnlyMode = false)
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
    (hFresh : ∀ i, nullifier nullifyingKey (leavesIndices i) ∉ s.spent)
    {rest : List CommitmentPreimage}
    (hLive : removeAll (s.live token)
        (List.ofFn fun i =>
          (⟨npk (masterPublicKey publicKey nullifyingKey) (randomIn i), token, valueIn i⟩ :
            CommitmentPreimage))
        = some rest) :
    ∃ s', Step s s' := by
  let pub : TransactPublic N M :=
    { merkleRoot := root, boundParamsHash := boundParamsHash,
      nullifiers := fun i => nullifier nullifyingKey (leavesIndices i),
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
      have hmap := distinct_leaves_distinct_nullifiers nullifyingKey (List.ofFn leavesIndices)
        hDistinctLeaves
      have heq : (List.ofFn leavesIndices).map (nullifier nullifyingKey)
          = List.ofFn (fun i => nullifier nullifyingKey (leavesIndices i)) := List.map_ofFn
      rwa [heq] at hmap)
    (show ∀ n ∈ List.ofFn (fun i => nullifier nullifyingKey (leavesIndices i)), n ∉ s.spent by
      intro n hn
      obtain ⟨i, hi⟩ := List.mem_ofFn.mp hn
      rw [← hi]
      exact hFresh i)
  refine ⟨_, Step.transact w pub hN hM hC
    (List.ofFn fun j => (⟨npkOut j, token, valueOut j⟩ : CommitmentPreimage)) [] rest spent'
    newRoot [] hEmergency (fun _ => hNotWithdrawOnly) hRoot (by simp [transactAllOutputs, w])
    (by simp) hLive hMark (by simp)⟩

/-- **Can happen: an unshield succeeds.** The degenerate single-output shape of
    `transact_can_happen`: a real key holder spends `N` genuinely-held, genuinely-live
    notes and the circuit's one output is the unshield payout itself (`newNotes := []`,
    the entire spent value becomes the unshield payout) — `_validateTransaction`'s
    unshield checks (TransactModule.sol:295-331; see the Zokyo 2022-12-21 finding #1
    cited at `Step.transact`) are exactly what licenses reading the circuit's one output
    as the payout amount. -/
theorem unshield_can_happen {s : PoolState} (hComplete : TransactProofCompleteness)
    (hSig : HonestSignature) {N : Nat} (publicKey : Nat × Nat)
    (nullifyingKey token boundParamsHash root newRoot : Nat)
    (randomIn valueIn : Fin N → Nat) (leavesIndices : Fin N → Nat)
    (pathElements : Fin N → List (Nat × Bool)) (npkOut valueOut : Nat)
    (hN : N ≤ 8)
    (hEmergency : s.emergencyPaused = false) (hRoot : root ∈ s.roots)
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
    (hFresh : ∀ i, nullifier nullifyingKey (leavesIndices i) ∉ s.spent)
    {rest : List CommitmentPreimage}
    (hLive : removeAll (s.live token)
        (List.ofFn fun i =>
          (⟨npk (masterPublicKey publicKey nullifyingKey) (randomIn i), token, valueIn i⟩ :
            CommitmentPreimage))
        = some rest) :
    ∃ s', Step s s' := by
  let pub : TransactPublic N 1 :=
    { merkleRoot := root, boundParamsHash := boundParamsHash,
      nullifiers := fun i => nullifier nullifyingKey (leavesIndices i),
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
      have hmap := distinct_leaves_distinct_nullifiers nullifyingKey (List.ofFn leavesIndices)
        hDistinctLeaves
      have heq : (List.ofFn leavesIndices).map (nullifier nullifyingKey)
          = List.ofFn (fun i => nullifier nullifyingKey (leavesIndices i)) := List.map_ofFn
      rwa [heq] at hmap)
    (show ∀ n ∈ List.ofFn (fun i => nullifier nullifyingKey (leavesIndices i)), n ∉ s.spent by
      intro n hn
      obtain ⟨i, hi⟩ := List.mem_ofFn.mp hn
      rw [← hi]
      exact hFresh i)
  refine ⟨_, Step.transact w pub hN (by omega) hC []
    (List.ofFn fun (_ : Fin 1) => (⟨npkOut, token, valueOut⟩ : CommitmentPreimage)) rest
    spent' newRoot [] hEmergency (fun h => absurd h (by simp)) hRoot
    (by simp [transactAllOutputs, w]) (by simp) hLive hMark (by simp)⟩

/-- **Can happen: an owned transact succeeds.** Directly wires an owned witness,
    constructed exactly as `ArmadaLean.PoolOwned.owned_spend_can_happen` builds one
    (inlined here, not obtained from that theorem's existential, for the same
    definitional-transparency reason as `transact_can_happen`), into
    `Step.transactOwned`: `hLive` supplies the ghost liveness precondition (the owner's
    notes are the model's own record of what it minted for them), `hN`/`hM` the
    registered-shape bound, `caller`/`hCaller` the authorization check
    (`ArmadaLean.PoolSafety.transactOwned_spends_only_owned` is the matching safety
    theorem). -/
theorem owned_transact_can_happen {s : PoolState} (hComplete : OwnedProofCompleteness)
    {N M : Nat} (ownerField token boundParamsHash root newRoot : Nat)
    (randomIn valueIn : Fin N → Nat) (leavesIndices : Fin N → Nat)
    (pathElements : Fin N → List (Nat × Bool)) (npkOut valueOut : Fin M → Nat)
    (hN : N ≤ 8) (hM : M ≤ 4)
    (hEmergency : s.emergencyPaused = false) (hNotWithdrawOnly : s.withdrawOnlyMode = false)
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
    (hOutputsNonZero : ∀ j, npkOut j ≠ 0)
    (caller : Nat) (hCaller : caller = addressOf ownerField)
    {rest : List CommitmentPreimage}
    (hLive : removeAll (s.live token)
        (List.ofFn fun i =>
          (⟨npk ownerField (randomIn i), token, valueIn i⟩ : CommitmentPreimage))
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
  have _ := hOutputsNonZero
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
  refine ⟨_, Step.transactOwned w pub hN hM hC caller hCaller rest spent' newRoot
    (List.ofFn fun j => (commitment (npkOut j) token (valueOut j),
      (⟨npkOut j, token, valueOut j⟩ : CommitmentPreimage)))
    hEmergency hNotWithdrawOnly hRoot hLive hMark ?_⟩
  intro cp hcp
  obtain ⟨j, hj⟩ := List.mem_ofFn.mp hcp
  rw [← hj]
  rfl
