import Lake
open Lake DSL

package «armada-lean» where

-- Mathlib is used wherever it applies (operator ruling 2026-10-27).
-- Pinned to the toolchain tag, the same pin EVMLean uses.
require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.33.1"

@[default_target]
lean_lib «ArmadaLean» where
  -- `ArmadaLean.Machines` (`ArmadaLean/Machines.lean`) is a second root, not
  -- an import of `ArmadaLean`: it imports `ArmadaLean` itself, to scan the
  -- whole checked environment for `Machine` values, so `lake build` must
  -- build it independently (`ArmadaLean.lean` cannot import it back without
  -- a cycle). See `ArmadaLean/Machines.lean`'s own doc comment.
  roots := #[`ArmadaLean, `ArmadaLean.Machines]
