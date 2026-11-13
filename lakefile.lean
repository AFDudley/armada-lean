import Lake
open Lake DSL

package «armada-lean» where
  -- Lake's content-addressed artifact cache. The default reads the cache and
  -- never writes it (Lake/Config/Monad.lean, `isArtifactCacheWritable`), so a
  -- fresh tree compiled all of ArmadaLean from source. The cache key is the
  -- source hash, the import hashes, the Lean git hash, the options and the
  -- module name; no absolute path. Two trees at different paths share one
  -- store. `restoreAllArtifacts` copies the `.olean` files too; without it
  -- Lake restores only the `.ilean` files and `lake env lean` in
  -- `scripts/gate_extra.py` has no imports. Measured 2026-11-08 at c3e423e2:
  -- fresh tree without the cache 244.9 s and 91 modules compiled; fresh tree
  -- with a warm store 8.9 s and 0 modules compiled. The store is
  -- `LAKE_CACHE_DIR` (default `~/.elan/toolchains/<toolchain>/lake/cache`).
  enableArtifactCache := true
  restoreAllArtifacts := true

-- Mathlib is used wherever it applies.
-- Pinned to the toolchain tag, the same pin EVMLean uses.
require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.35.0"

@[default_target]
lean_lib «ArmadaLean» where
  -- `ArmadaLean.Machines` (`ArmadaLean/Machines.lean`) is a second root, not
  -- an import of `ArmadaLean`: it imports `ArmadaLean` itself, to scan the
  -- whole checked environment for `Machine` values, so `lake build` must
  -- build it independently (`ArmadaLean.lean` cannot import it back without
  -- a cycle). See `ArmadaLean/Machines.lean`'s own doc comment.
  -- Mathlib's `says` re-runs every recorded search when the environment variable `CI`
  -- is set (`Mathlib/Tactic/Says.lean`). Agent shells here set `CI=true`, which doubled
  -- the search cost of every build (measured 2026-10-31). Normal builds run only the
  -- recorded proof; `scripts/verify_says.sh` re-verifies on purpose
  -- (`-Dsays.verify=true`). type-doctrine.md section 4a rule 5.
  leanOptions := #[⟨`weak.says.no_verify_in_CI, true⟩]
  roots := #[`ArmadaLean, `ArmadaLean.Machines]
