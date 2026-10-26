/-
  Nitro protocol specification: ledger channels, sub-channels and virtual
  channels as network-state constructions. Sources: Nitro §5.3-5.4 (lines
  847-1047) and §6.3-6.5 (lines 1257-1455). SATP §3 (lines 373-485) gives
  the virtual channel construction with guarantee items and `reclaim`; that
  form is in `SATP.lean`. This file keeps Nitro's guarantee-channel form,
  which SATP and go-nitro do not have, for the Nitro §6.4 offload results.
  See `Address.lean` for the source list.

  Nitro:694-709 ("Outcomes First"): a construction is written as a set of
  outcomes, each finalizable by the listed participants, plus the balances
  held on-chain. The predicates below read a family of views that way.
-/
import ArmadaLean.Nitro.Value

namespace ArmadaLean.Nitro

/-- A participant's address. -/
def Participant.address (p : Participant) : Address := .participant p

/-- Nitro:857 `⟦L : x⟧`: every view sees balance `x` at `a`. -/
def Views.HoldsBalance (v : Views) (a : Address) (x : Coins) : Prop :=
  ∀ p, (v p).chain.balances.get a = x

/-- Nitro:592-593 `[χ ↦ Ω]_{p1,...,pm}`: `Ω` is finalizable in `χ` by each
    listed participant. -/
def Views.FinalizableBy (apps : Apps) (Ts : Threats apps) (v : Views) (c : FixedPart)
    (Ω : Outcome) (ps : List Participant) : Prop :=
  ∀ p ∈ ps, Finalizable apps (Ts.T p) c Ω (v p)

/-- An allocation entry `A : a`. -/
def alloc (a : Address) (x : Coins) : Entry := ⟨a, .alloc x⟩

/-- Nitro:848-851: "A ledger channel is a channel whose sole purpose is to
    provide funding to other channels... All ledger channels run the consensus
    game." -/
def IsLedgerChannel (apps : Apps) (c : FixedPart) : Prop :=
  apps c.appDef = consensusRules

/-- Nitro:857 (equation 2): `⟦L : 10⟧, [L ↦ (A : 3, B : 1, χ : 6)]_{A,B}`, in
    general `⟦L : x⟧, [L ↦ (A : a, B : b, χ : c)]_{A,B}` (Nitro:945, eq 6). -/
structure LedgerWithSub where
  A : Participant
  B : Participant
  L : FixedPart
  χ : FixedPart
  a : Coins
  b : Coins
  c : Coins

/-- The ledger outcome `(A : a, B : b, χ : c)`. -/
def LedgerWithSub.outcome (w : LedgerWithSub) : Outcome :=
  .allocation [alloc w.A.address w.a, alloc w.B.address w.b, alloc w.χ.address w.c]

/-- Nitro:945 (eq 6) holds in the views: `L` holds `a + b + c` and the outcome
    is finalizable by `A` and `B`. -/
def LedgerWithSub.Holds (apps : Apps) (Ts : Threats apps) (v : Views) (w : LedgerWithSub) :
    Prop :=
  IsLedgerChannel apps w.L ∧ w.L.participants = [w.A, w.B] ∧
  v.HoldsBalance w.L.address (w.a + w.b + w.c) ∧
  v.FinalizableBy apps Ts w.L w.outcome [w.A, w.B]

/-- Nitro:1261-1270 and Nitro:1273-1284 (Figure 24): the virtual channel
    construction. Ledger channels `L` (A, I) and `L'` (B, I), joint channel
    `J` (A, B, I), guarantor channels `G` and `G'` that target `J`, and the
    virtual channel `χ` (A, B). `x = a + b`. -/
structure VirtualSetup where
  A : Participant
  B : Participant
  I : Participant
  L : FixedPart
  L' : FixedPart
  J : FixedPart
  G : FixedPart
  G' : FixedPart
  χ : FixedPart
  x : Coins

/-- Nitro:1275 `[L ↦ (G : x)]_{A,I}`. -/
def VirtualSetup.ledgerOutcome (w : VirtualSetup) : Outcome :=
  .allocation [alloc w.G.address w.x]

/-- Nitro:1275 `[L' ↦ (G' : x)]_{B,I}`. -/
def VirtualSetup.ledgerOutcome' (w : VirtualSetup) : Outcome :=
  .allocation [alloc w.G'.address w.x]

/-- Nitro:1278 `[G ↦ (J|χ, A, I)]_{A,I}`. -/
def VirtualSetup.guaranteeOutcome (w : VirtualSetup) : Outcome :=
  .guarantee w.J.address [w.χ.address, w.A.address, w.I.address]

/-- Nitro:1278 `[G' ↦ (J|χ, B, I)]_{B,I}`. -/
def VirtualSetup.guaranteeOutcome' (w : VirtualSetup) : Outcome :=
  .guarantee w.J.address [w.χ.address, w.B.address, w.I.address]

/-- Nitro:1280 `[J ↦ (χ : x, I : x)]_{A,B,I}`. -/
def VirtualSetup.jointOutcome (w : VirtualSetup) : Outcome :=
  .allocation [alloc w.χ.address w.x, alloc w.I.address w.x]

/-- The channel participant lists of Figure 24. -/
def VirtualSetup.WellFormed (w : VirtualSetup) : Prop :=
  w.L.participants = [w.A, w.I] ∧ w.L'.participants = [w.B, w.I] ∧
  w.J.participants = [w.A, w.B, w.I] ∧ w.G.participants = [w.A, w.I] ∧
  w.G'.participants = [w.B, w.I] ∧ w.χ.participants = [w.A, w.B] ∧
  w.A ≠ w.B ∧ w.A ≠ w.I ∧ w.B ≠ w.I ∧
  w.L ≠ w.L' ∧ w.L ≠ w.J ∧ w.L ≠ w.G ∧ w.L ≠ w.G' ∧ w.L ≠ w.χ ∧
  w.L' ≠ w.J ∧ w.L' ≠ w.G ∧ w.L' ≠ w.G' ∧ w.L' ≠ w.χ ∧
  w.J ≠ w.G ∧ w.J ≠ w.G' ∧ w.J ≠ w.χ ∧ w.G ≠ w.G' ∧ w.G ≠ w.χ ∧ w.G' ≠ w.χ

/-- Nitro:1273-1280 (Figure 24) holds in the views: `⟦L : x, L' : x⟧` and the
    five finalizable outcomes. -/
def VirtualSetup.Holds (apps : Apps) (Ts : Threats apps) (v : Views) (w : VirtualSetup) : Prop :=
  w.WellFormed ∧
  v.HoldsBalance w.L.address w.x ∧ v.HoldsBalance w.L'.address w.x ∧
  v.FinalizableBy apps Ts w.L w.ledgerOutcome [w.A, w.I] ∧
  v.FinalizableBy apps Ts w.L' w.ledgerOutcome' [w.B, w.I] ∧
  v.FinalizableBy apps Ts w.G w.guaranteeOutcome [w.A, w.I] ∧
  v.FinalizableBy apps Ts w.G' w.guaranteeOutcome' [w.B, w.I] ∧
  v.FinalizableBy apps Ts w.J w.jointOutcome [w.A, w.B, w.I]

/-- Nitro:1264 (equation 22): the starting point `⟦L : x, L' : x⟧,
    [L ↦ (A : a, I : b)]_{A,I}, [L' ↦ (B : b, I : a)]_{B,I}` with
    `x = a + b`. -/
def VirtualSetup.Start (apps : Apps) (Ts : Threats apps) (v : Views) (w : VirtualSetup)
    (a b : Coins) : Prop :=
  w.WellFormed ∧ w.x = a + b ∧
  v.HoldsBalance w.L.address w.x ∧ v.HoldsBalance w.L'.address w.x ∧
  v.FinalizableBy apps Ts w.L (.allocation [alloc w.A.address a, alloc w.I.address b]) [w.A, w.I] ∧
  v.FinalizableBy apps Ts w.L' (.allocation [alloc w.B.address b, alloc w.I.address a]) [w.B, w.I]

/-- Nitro:1427-1429 (equations 42-43): the closed state
    `[L ↦ (A : a', I : b')]_{A,I}, [L' ↦ (B : b', I : a')]_{B,I}`. -/
def VirtualSetup.Closed (apps : Apps) (Ts : Threats apps) (v : Views) (w : VirtualSetup)
    (a' b' : Coins) : Prop :=
  v.FinalizableBy apps Ts w.L (.allocation [alloc w.A.address a', alloc w.I.address b']) [w.A, w.I] ∧
  v.FinalizableBy apps Ts w.L' (.allocation [alloc w.B.address b', alloc w.I.address a']) [w.B, w.I]

/-- Two network states have the same value for a participant. Nitro:505-509:
    "the sequence of state transitions is value preserving for each
    participant involved". -/
def SameValue (apps : Apps) {p : Participant} (T : Threat p) (net net' : NetworkState p) : Prop :=
  ∀ x, Value apps T net x ↔ Value apps T net' x

end ArmadaLean.Nitro
