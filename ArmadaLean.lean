/-
  Armada Lean — formal verification of shielded-pool security properties.
  Root module: imports all verified components.
-/
import ArmadaLean.Field
import ArmadaLean.Poseidon
import ArmadaLean.Token
import ArmadaLean.BoundParams
import ArmadaLean.RangeCheck
import ArmadaLean.ValueConservation
import ArmadaLean.Nullifier
import ArmadaLean.Merkle
import ArmadaLean.Transact
import ArmadaLean.TransactOwned
import ArmadaLean.PoolOwned
import ArmadaLean.Pool
import ArmadaLean.PoolSafety
import ArmadaLean.Vault
import ArmadaLean.Fee
-- Nitro protocol specification (S1 ForceMove, S2 Nitro, S3 SATP); see docs/nitro-theorems.md
import ArmadaLean.Nitro.Address
import ArmadaLean.Nitro.Outcome
import ArmadaLean.Nitro.Channel
import ArmadaLean.Nitro.Adjudicator
import ArmadaLean.Nitro.Strategy
import ArmadaLean.Nitro.Value
import ArmadaLean.Nitro.Constructions
import ArmadaLean.Nitro.SATP
import ArmadaLean.Nitro.Safety
import ArmadaLean.Nitro.Liveness
-- Armada adjudicator: Nitro over Armada pool notes; see docs/armada-nitro-theorems.md
import ArmadaLean.ArmadaNitro.Notes
import ArmadaLean.ArmadaNitro.State
import ArmadaLean.ArmadaNitro.Operations
import ArmadaLean.ArmadaNitro.Refinement
import ArmadaLean.ArmadaNitro.Safety
import ArmadaLean.ArmadaNitro.Strategy
import ArmadaLean.ArmadaNitro.Liveness
