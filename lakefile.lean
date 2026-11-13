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

-- Mathlib is used wherever it applies (operator ruling 2026-10-27).
-- Pinned to the toolchain tag, the same pin EVMLean uses.
require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.35.0"

-- The Lean half of exophial's Lean spec-checking procedure
-- (#check_spec_bindings, spec_premise%, #spec_report), vendored at
-- vendor/exophial_core/ (docs/merge_plan.md Stage ML, "Where each part
-- belongs": "A Lean package that exophial ships"). A git dependency does
-- not work here: the commit-boundary gate container builds with no
-- bind mount and no inherited host environment (exophial
-- docs/decisions/2026-10-14-gate-runs-in-a-container-built-from-the-judged-commit.md
-- D49.5/D49.6), and exophial's own GitHub repository needs a credential
-- the gate build never carries (exo-??? -- filed). exophial's README/
-- CLAUDE.md names subtree-vendoring, not only a lake git dependency, as
-- the sanctioned distribution route for a consuming repository; this
-- follows that route for the Lean half. The vendored copy is
-- exophial_core/ unchanged from exophial commit
-- 21517119daa04c9cce6eb32c77479ecc194afdcb (exo-218, exo-748 family
-- ships the package; re-vendor once exo-2439/exo-6d7a merge there).
require exophial_core from "vendor/exophial_core"

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
