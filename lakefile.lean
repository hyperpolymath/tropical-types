-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell

import Lake
open Lake DSL

/-- Pure core Lean 4 proofs (no Mathlib dependency).
    Toolchain is pinned to `leanprover/lean4:v4.35.0` in `lean-toolchain`. -/
package «tropical-resource-typing» where

@[default_target]
lean_lib Tropical where
  srcDir := "."
  -- The two order-reversing twins: max-plus session grading and the
  -- min-max (bottleneck) transport semiring.
  roots := #[`TropicalSessionTypes, `TropicalAdapterPath]

/-- The consumer-facing **resource-grade axis**: a reusable ordered
    semiring / resource-algebra interface (`Resource.Algebra.*`), concrete
    instances (`Resource.Instances.*`), the parametric transport theorem, the
    infinite-carrier stress test, and the (echo-free) residue-measure bridge.

    `globs` pulls in every `Resource.*` submodule so the whole axis builds as a
    unit; the aggregator `Resource.lean` re-exports them for downstream import. -/
@[default_target]
lean_lib Resource where
  srcDir := "."
  roots := #[`Resource]
  globs := #[.andSubmodules `Resource]
