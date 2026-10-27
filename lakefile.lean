import Lake
open Lake DSL

package «armada-lean» where

-- Mathlib is used wherever it applies (operator ruling 2026-10-27).
-- Pinned to the toolchain tag, the same pin EVMLean uses.
require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.33.1"

@[default_target]
lean_lib «ArmadaLean» where
