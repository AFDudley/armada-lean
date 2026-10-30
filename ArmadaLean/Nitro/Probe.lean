import ArmadaLean.Nitro.Liveness
namespace ArmadaLean.Nitro
variable {E : Type} [DecidableEq E]

theorem probe {apps : Apps E} {p : Participant} {T : Threat E p} {c : FixedPart} {Ω : Outcome E} :
    ∀ {net net' : NetworkState E p} {t : Time} {pending : List (Op E)},
      Threat.RoundSeq apps T t pending net net' →
      net'.chain.finalizedWith c.address = some Ω →
      net.chain.finalOutcome c.address = none →
      False := by
  intro net net' t pending hseq
  induction hseq with
  | nil =>
    rename_i net2
    intro hΩfinal hnone
    sorry
  | @land pending net1 net2 op l1 l2 hsplit hrest ih => intro _ _; sorry
  | @tick pending net1 net2 dt hfeas hgate hrest ih => intro _ _; sorry
  | @other pending net1 net2 m hfeas hnotick hnoland hrest ih => intro _ _; sorry

end ArmadaLean.Nitro
