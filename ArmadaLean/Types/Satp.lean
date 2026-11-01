/-
  Refined SATP route types. `docs/lean/type-doctrine.md` rule 1: a condition that two or
  more statements need is a type.
-/
import ArmadaLean.Nitro.SATP

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

end ArmadaLean.Nitro
