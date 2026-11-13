/-
  Refined SATP route types. `docs/lean/type-doctrine.md` rule 1: a condition that two or
  more statements need is a type.
-/
import ArmadaLean.Nitro.SATP
import ArmadaLean.Types.Channel

namespace ArmadaLean.Nitro

variable {E : Type} [DecidableEq E]

/-- The parties of the SATP virtual channel `r.V` (SATP:405-409, Protocol 3.1: `V` runs
    from Alice to Bob over the route's peers): `alice` is `V`'s first participant, `bob`
    its last, and `P`, whose network the statement reads, is one of its participants.
    Every helper of the `r.V` finalization sub-game (`Nitro/Liveness.lean`,
    `satp_virtual_finalize_aux` and the lemmas it calls) states these three facts, so they
    are one premise. `satp_theorem_3_2` obtains them from `Route.WellFormed`
    (`r.V.participants = r.peers`) and its own `halice`/`hbob`/`hP`. -/
structure SatpEnds (r : Route E) (alice bob P : Participant) : Prop where
  /-- `alice` is `r.V`'s first participant. -/
  head : r.V.participants.head? = some alice
  /-- `bob` is `r.V`'s last participant. -/
  last : r.V.participants.getLast? = some bob
  /-- `P` is a participant of `r.V`. -/
  mem : P ∈ r.V.participants

/-- The SATP virtual channel `r.V` as its finalization sub-game reads it: its parties
    (`SatpEnds`), its app, and its challenge duration. The `r.V` helpers of
    `Nitro/Liveness.lean` state these facts together. -/
structure SatpVirtual (apps : Apps E) (ε : Time) (r : Route E) (alice bob P : Participant) :
    Prop extends SatpEnds r alice bob P where
  /-- `r.V` runs the SATP virtual app. -/
  app : apps r.V.appDef = satpVirtualRules
  /-- `r.V`'s challenge duration covers two round delays of `ε`. -/
  timed : r.V.IsTimed ε

/-- A candidate state of `r.V` with a support proof that `r.V`'s rules accept
    (`satpVirtualRules.supports`). A `challenge` or `checkpoint` on `r.V` submits one; the
    `r.V` finalization helpers (`satpVirtual_channel`, `satpVirtual_supported`,
    `satp_land_keeps_status`) read the proof, the candidate and the support check together,
    so the three are one value. -/
structure SatpCandidate (r : Route E) where
  /-- The support proof. -/
  proof : SupportProof E
  /-- The candidate state. -/
  cand : State E
  /-- `r.V`'s rules accept `proof` for `cand`. -/
  supports : satpVirtualRules.supports r.V proof cand = true

/-- `r.V` is challenged in `net`'s chain at turn record `u` with challenge `ch`. The
    `r.V` wait step (`satp_wait_resolves_or_escalates`, `satp_virtual_wait_step`) and the
    pair-outcome lemma for a challenged `r.V` (`satpVirtual_challenged_outcome_pair`) start
    from this record. -/
structure SatpChallenged {P : Participant} (r : Route E) (net : NetworkState E P) (u : Nat)
    (ch : Challenge E) : Prop where
  /-- `r.V`'s on-chain status. -/
  status : net.chain.statusOf r.V = .challenged u ch

/-- A ledger outcome after Round 2 of Protocol 3.1 (SATP:411-418) for the ledger between
    `P` (left) and `Q` (right), with the balance `bal` of `D` before Round 2 and the amount
    `debit` Round 2 took from it (`Route.LedgerAfterRound2`). `satp_theorem_3_2` (both
    ledgers of an intermediary) and `satp_end_user_recovers` (Alice's ledger) state this
    fact, so it is one type (`docs/lean/type-doctrine.md` rule 1). -/
structure Route.Round2Ledger (r : Route E) (P Q D : Participant) (debit : Coins) where
  /-- The ledger's allocation after Round 2. -/
  outcome : Allocation E
  /-- The balance of `D` before Round 2. -/
  bal : Coins
  /-- `outcome` is the Round 2 outcome for `bal` and `debit`. -/
  afterRound2 : r.LedgerAfterRound2 outcome P Q D bal debit

end ArmadaLean.Nitro
