/-
  Nitro protocol specification: ledger channels and sub-channels as
  network-state constructions. Source: Nitro §5.3-5.4 (lines 847-1047). The
  virtual channel construction is SATP §3 (lines 373-485), with guarantee
  items and `reclaim`, in `SATP.lean`. Nitro §6.3-6.5's guarantee-channel
  construction is not modelled (operator ruling 2026-10-27). See
  `Address.lean` for the source list.

  Nitro:694-709 ("Outcomes First"): a construction is written as a set of
  outcomes, each finalizable by the listed participants, plus the balances
  held on-chain. The predicates below read a family of views that way.
  Destinations are external destinations of type `E` (operator ruling
  2026-10-27); each participant of a construction names its own.
-/
import ArmadaLean.Nitro.Value

namespace ArmadaLean.Nitro

variable {E : Type} [DecidableEq E]

/-- Nitro:857 `⟦L : x⟧`: every view sees balance `x` at `a`. -/
def Views.HoldsBalance (v : Views E) (a : Address E) (x : Coins) : Prop :=
  ∀ p, (v p).chain.balances.get a = x

/-- Nitro:592-593 `[χ ↦ Ω]_{p1,...,pm}`: `Ω` is finalizable in `χ` by each
    listed participant. -/
def Views.FinalizableBy (apps : Apps E) (Ts : Threats E apps) (v : Views E) (c : FixedPart)
    (Ω : Outcome E) (ps : List Participant) : Prop :=
  ∀ p ∈ ps, Finalizable apps (Ts.T p) c Ω (v p)

/-- An allocation entry `A : a`. -/
def alloc (a : Address E) (x : Coins) : Entry E := ⟨a, .alloc x⟩

/-- Nitro:848-851: "A ledger channel is a channel whose sole purpose is to
    provide funding to other channels... All ledger channels run the consensus
    game." -/
def IsLedgerChannel (apps : Apps E) (c : FixedPart) : Prop :=
  apps c.appDef = consensusRules

/-- Nitro:857 (equation 2): `⟦L : 10⟧, [L ↦ (A : 3, B : 1, χ : 6)]_{A,B}`, in
    general `⟦L : x⟧, [L ↦ (A : a, B : b, χ : c)]_{A,B}` (Nitro:945, eq 6).
    `dA` and `dB` are the external destinations of `A` and `B`. -/
structure LedgerWithSub (E : Type) where
  A : Participant
  B : Participant
  dA : E
  dB : E
  L : FixedPart
  χ : FixedPart
  a : Coins
  b : Coins
  c : Coins

/-- The ledger outcome `(A : a, B : b, χ : c)`. -/
def LedgerWithSub.outcome (w : LedgerWithSub E) : Outcome E :=
  .allocation [alloc (.external w.dA) w.a, alloc (.external w.dB) w.b, alloc w.χ.address w.c]

/-- Nitro:945 (eq 6) holds in the views: `L` holds `a + b + c` and the outcome
    is finalizable by `A` and `B`. -/
def LedgerWithSub.Holds (apps : Apps E) (Ts : Threats E apps) (v : Views E) (w : LedgerWithSub E) :
    Prop :=
  IsLedgerChannel apps w.L ∧ w.L.participants = [w.A, w.B] ∧
  v.HoldsBalance w.L.address (w.a + w.b + w.c) ∧
  v.FinalizableBy apps Ts w.L w.outcome [w.A, w.B]

/-- Two network states have the same value at the destination `d`.
    Nitro:505-509: "the sequence of state transitions is value preserving for
    each participant involved". -/
def SameValue (apps : Apps E) {p : Participant} (T : Threat E p) (d : E)
    (net net' : NetworkState E p) : Prop :=
  ∀ x, Value apps T d net x ↔ Value apps T d net' x

end ArmadaLean.Nitro
