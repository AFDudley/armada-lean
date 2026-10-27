/-
  Armada adjudicator: the pool interface. The Armada adjudicator is Nitro
  (`ArmadaLean/Nitro/`) whose escrowed assets are notes in the Armada pool
  (`ArmadaLean/Pool.lean`). Design record and theorem map:
  `docs/armada-nitro-theorems.md`.

  The adjudicator is an ordinary pool user (operator ruling 2026-10-27, 2;
  labbook `2026-10-18-contract-owned-notes-and-zk-channel-apps.md`, decision 9).
  It calls the pool's own `Step`. It never restates the pool's state update
  (`armada-laconic/docs/lean/writing-lean.md`, rule 1; layout audit finding
  A10). A pool call is described by its effect on the pool's live notes
  (`PoolCall`): the notes it spends and the notes it creates. Every pool
  theorem about `Step` then applies to the call.

  This layer has no contract layout and no encoding (operator ruling
  2026-10-27, 1). The adjudicator has an address term `Config.self`, not a
  derivation from creation inputs (audit finding A2). No circuit width
  appears here: the pool's input and output limits stay in the pool, behind
  the hypothesis `PoolExecutes`.
-/
import ArmadaLean.PoolSafety
import ArmadaLean.Nitro.Liveness

namespace ArmadaLean.ArmadaNitro

set_option autoImplicit false

open ArmadaLean.Nitro (Coins Participant)

/-- A pool note as the pool identifies it: its `(treeNumber, position)` key and
    its preimage. `PoolState.live t` lists these entries (Pool.lean:855-875);
    two notes with one preimage differ by key (Pool.lean:22-31). -/
abbrev Note := (Nat × Nat) × CommitmentPreimage

/-- The value of a note (`CommitmentPreimage.value`, PoolOwned.lean:73-77). -/
def Note.value (e : Note) : Coins := e.2.value

/-- The total value of a list of notes. -/
def notesValue (es : List Note) : Coins := (es.map Note.value).sum

/-- The fixed data of one Armada adjudicator deployment.
    * `self`: the adjudicator's address. Its notes have note keys
      `npk self r` (TransactOwned.circom:66-70; `ArmadaLean.Transact.npk`).
    * `self_isContract`: the address is a Keccak term, the pool's convention
      for a contract address (PoolOwned.lean, module comment on address terms).
      With `user_npk_ne_contract_npk` (TransactOwned.lean:196) no user note
      key equals an adjudicator note key.
    * `payeeKey p`: the note key at which participant `p` is paid (operator
      ruling 2026-10-27, 4).
    * `payeeKey_user`: that key is a user note key, so `p` spends the note with
      its own spending key (Transact.circom:74-84).
    * `minCredit`: the minimum credit into a channel that is already finalized
      (operator ruling 2026-10-27, armada-laconic
      `labbook/2026-10-27-payout-griefing.md`). It is a deploy-time parameter,
      like the pool's `FeeRatio`. Every step takes the same `Config`, so no
      step changes it. Its value is open. -/
structure Config where
  self : Term
  self_isContract : ∃ inputs, self = Term.keccak inputs
  payeeKey : Participant → Term
  payeeKey_user : ∀ p, ∃ pk nk r, payeeKey p = npk (masterPublicKey pk nk) r
  minCredit : Coins

/-- A preimage is keyed to `owner`: its note key is `npk owner r` for some
    randomness `r` (TransactOwned.circom:66-70). Only `owner` can spend such a
    note (`owned_owner_binding`, PoolOwned.lean:137). -/
def OwnedBy (owner : Term) (pre : CommitmentPreimage) : Prop :=
  ∃ r, pre.npk = npk owner r

/-- The step from `s` to `s'` creates the note `e` of token `t`: `e` was not
    live before the step and is live after it. The dual of the pool's
    `Spends` (PoolSafety.lean:1782). -/
def Creates (s s' : PoolState) (t : Token) (e : Note) : Prop :=
  e ∉ s.live t ∧ e ∈ s'.live t

/-- One pool call with an exact note-level effect on token `t`: a pool `Step`
    that spends exactly the notes `ins` and creates exactly the notes `outs`.
    The pool decides the keys of the created notes (`insertTree`,
    `insertStart`, Pool.lean:595-602). A caller names them only after the
    call. -/
structure PoolCall (ps ps' : PoolState) (t : Token) (ins outs : List Note) : Prop where
  step : _root_.Step ps ps'
  spends : ∀ e, Spends ps ps' t e ↔ e ∈ ins
  creates : ∀ e, Creates ps ps' t e ↔ e ∈ outs

/-- A pool step by a caller other than the adjudicator. The pool's `Step` does
    not name its caller. Owner binding gives the consequence that matters: a
    step that spends a note keyed to `self` has caller `self`
    (`transactOwned_spends_only_owned`, PoolSafety.lean:205), and a plain
    transact cannot spend such a note (`transact_spends_only_owned`,
    PoolSafety.lean:186, with `user_npk_ne_contract_npk`). So a step by any
    other caller spends no note keyed to `self`. This definition states that
    consequence as the rule for the environment. -/
def OtherUserStep (self : Term) (ps ps' : PoolState) : Prop :=
  _root_.Step ps ps' ∧ ∀ t e, Spends ps ps' t e → ¬ OwnedBy self e.2

/-- The pool executes an owned spend of `ins`, for every list of output
    preimages of token `t` with the same total value. The created notes carry
    exactly those preimages. -/
def OwnedSpendable (ps : PoolState) (t : Token) (ins : List Note) : Prop :=
  ∀ outs : List CommitmentPreimage,
    (outs.map CommitmentPreimage.value).sum = notesValue ins →
    (∀ o ∈ outs, o.token = t) →
    ∃ ps' news, PoolCall ps ps' t ins news ∧ news.map Prod.snd = outs

/-- The pool interface that the liveness theorems assume: in every reachable
    pool state, the pool executes every owned spend of live, distinct notes
    keyed to the adjudicator. `owned_merge_can_happen` (PoolSafety.lean:1864)
    gives this for one output, at most 8 inputs in one tree, and a sum that
    passes the range check `Spendable`. The general form is a hypothesis, not a
    theorem: `docs/armada-nitro-theorems.md`, open design choice D1. -/
def PoolExecutes (cfg : Config) : Prop :=
  ∀ ps, _root_.Reachable ps → ∀ t (ins : List Note),
    (∀ e ∈ ins, e ∈ ps.live t ∧ OwnedBy cfg.self e.2) → ins.Nodup → ins ≠ [] →
    OwnedSpendable ps t ins

end ArmadaLean.ArmadaNitro
