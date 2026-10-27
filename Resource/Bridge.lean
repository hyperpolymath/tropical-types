-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
import Resource.Instances.MaxPlus
import Resource.Instances.MinMax
import TropicalSessionTypes
import TropicalAdapterPath

/-!
  # Bridges — the two original twins stand on the resource-grade axis

  Author: Jonathan D.A. Jewell (hyperpolymath)
  Verified: Lean 4.35.0 (pinned via `lean-toolchain`), no Mathlib.

  `TropicalSessionTypes.lean` (max-plus session grading) and
  `TropicalAdapterPath.lean` (min-max bottleneck paths) predate the `Resource.*`
  axis.  This module shows they are *instances* of it, closing the long-standing
  "construct a functor between the two structures" / "state the QTT quotient
  morphism" open items recorded in `docs/LEAN-FORMALIZATION.adoc` and the file
  headers.

  Everything here is by `rfl` or a one-line restatement — the point is that the
  axis operations *literally are* the operations the twins were already using, so
  the existing theorems (`soundness`, `tropical_grade_le_sequentialTotal`,
  `hub_ceiling`) are facts about the resource algebra.
-/

namespace Resource.Bridge

open scoped Resource.ResourceSemiring Resource.ResourceAlgebra

-- ============================================================================
-- 1.  MaxPlus  ⇄  TropicalSessionTypes  (session grading)
-- ============================================================================

section MaxPlus
open Hyperpolymath.Tropical
open Resource.Instances.MaxPlus

/-- The resource-algebra `⊞` on the max-plus carrier *is* session-grading `tAdd`. -/
theorem add_eq_tAdd (a b : Tropical) : (a ⊞ b) = tAdd a b := rfl
/-- The resource-algebra `⊠` on the max-plus carrier *is* session-grading `tMul`. -/
theorem mul_eq_tMul (a b : Tropical) : (a ⊠ b) = tMul a b := rfl
/-- The resource `zero` is `bot` (`−∞`). -/
theorem zero_eq_bot : (Resource.ResourceSemiring.zero : Tropical) = Tropical.bot := rfl
/-- The resource `one` is `val 0`. -/
theorem one_eq_val0 : (Resource.ResourceSemiring.one : Tropical) = Tropical.val 0 := rfl

/-- Speculative choice in `Session` is the resource-algebra choice `⊞`. -/
theorem grade_spec_par (s1 s2 : Session) :
    grade (.spec_par s1 s2) = (grade s1 ⊞ grade s2) := rfl

/-- Sending is sequential composition `⊠` with the unit-cost grade `val 1`. -/
theorem grade_send (s : Session) :
    grade (.send s) = (Tropical.val 1 ⊠ grade s) := rfl

/-- **The QTT refinement, inside the resource order.**  The static tropical grade
    of a session is `⊑` the naïve sequential billing.  This is
    `tropical_grade_le_sequentialTotal` re-expressed through `soundness` as a fact
    about `ResourceAlgebra.le` — the QTT refinement morphism the headers asked for. -/
theorem grade_le_sequential (s : Session) :
    (grade s) ⊑ (Tropical.val (sequentialTotal s)) := by
  rw [soundness s]
  exact (le_val_val (Span s) (sequentialTotal s)).mpr (tropical_grade_le_sequentialTotal s)

end MaxPlus

-- ============================================================================
-- 2.  MinMax  ⇄  TropicalAdapterPath  (bottleneck paths)
-- ============================================================================

section MinMax
open Hyperpolymath.ProtocolSquisher.Tropical
open Resource.Instances.MinMax
open Resource.Instances.MinMax.MinMax

/-- The bounded bottleneck `tcAdd` (`min`) embeds into the resource choice `⊞`. -/
theorem embed_tcAdd (m n : Nat) : val (tcAdd m n) = (val m ⊞ val n) := rfl
/-- The bounded bottleneck `tcMul` (`max`) embeds into resource composition `⊠`. -/
theorem embed_tcMul (m n : Nat) : val (tcMul m n) = (val m ⊠ val n) := rfl
/-- `tcOne` embeds as the resource `one`. -/
theorem embed_tcOne : val tcOne = (Resource.ResourceSemiring.one : MinMax) := rfl

/-- **The honesty gap.**  The bounded model's `tcZero` (the finite `1000000`
    stand-in for `+∞`) is NOT the resource `zero` (`top = +∞`).  The infinite
    carrier `Resource.Instances.MinMax` is the faithful one; `TropicalAdapterPath`'s
    numeric bound is an approximation that this embedding makes explicit. -/
theorem embed_tcZero_ne_zero : val tcZero ≠ (Resource.ResourceSemiring.zero : MinMax) := by
  decide

/-- **`hub_ceiling`, inside the resource order.**  A path's bottleneck grade is
    `⊑` (no better than) the grade of every edge it routes through — one shared
    hub caps the fidelity of everything passing through it.  This is
    `hub_ceiling` re-expressed as a fact about `ResourceAlgebra.le`. -/
theorem hub_ceiling_le (e : TransportClass) (path : AdapterPath) (h : e ∈ path) :
    (val (pathCost path)) ⊑ (val (grade e)) :=
  (le_val_val (pathCost path) (grade e)).mpr (hub_ceiling e path h)

end MinMax

end Resource.Bridge
