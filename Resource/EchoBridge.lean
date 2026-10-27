-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
import Resource.Algebra.Ordered
import Resource.Instances.MaxPlus

/-!
  # Bridge — a resource algebra may measure Echo residues

  Author: Jonathan D.A. Jewell (hyperpolymath)
  Verified: Lean 4.35.0 (pinned via `lean-toolchain`), no Mathlib.

  ## Boundary invariant (the whole point of this file)

  This module makes one direction precise and machine-checked:

      resource algebra  ──consumed by──▶  residue measure

  A *residue measure* maps an **opaque** residue carrier `E` into a resource
  algebra `R` of this repository, accumulating residues via `R`'s sequential
  composition `⊠`.  The arrow is `E → R`: the residue-measure construction
  *depends on* the resource algebra.

  It is **NOT** the other direction:

      Echo  ──is an instance of──▶  resource / soundness     (FALSE — never)

  * `E` here stands in for an Echo residue carrier.  It is required to be **no
    more than a plain type with a monoid of residues** — it is *not* a
    `ResourceAlgebra`, and nothing here makes it one.  Echo is a modality; it is
    not a resource-grade instance.
  * `R` is a genuine `ResourceAlgebra` (linear, affine, max-plus, min-plus,
    min-max — any instance from `Resource.Instances`).
  * This file imports **no** `echo-types` dependency (the repo has none).  `E` is
    abstract precisely so that an Echo residue interface downstream can supply it
    without this repo ever depending on Echo.

  So: Echo may consume a tropical (or any) resource algebra as a residue measure;
  that does not make Echo a resource instance, nor a soundness instance.
-/

namespace Resource

open scoped ResourceSemiring

/-- A **residue measure**: an opaque residue carrier `E` (think: Echo residues),
    with a way to combine residues (`combine`) and an empty residue (`empty`),
    measured into a resource algebra `R` so that the measure is a monoid
    homomorphism into `R`'s *sequential-composition* monoid `(⊠, one)`.

    `E` carries **no** `ResourceAlgebra` instance — it is just a type with a
    residue monoid.  Only `R` is a resource algebra.  The dependency direction is
    `E → R`. -/
structure ResidueMeasure (E : Type) (R : Type) [ResourceAlgebra R] where
  /-- How two residues accumulate (the Echo-side operation, opaque here). -/
  combine : E → E → E
  /-- The null residue. -/
  empty   : E
  /-- The measurement of a residue as a resource grade. -/
  measure : E → R
  /-- The empty residue measures as the multiplicative identity `one`. -/
  measure_empty   : measure empty = (ResourceSemiring.one : R)
  /-- Accumulating residues multiplies (sequentially composes) their grades. -/
  measure_combine : ∀ e₁ e₂ : E, measure (combine e₁ e₂) = measure e₁ ⊠ measure e₂

namespace ResidueMeasure

variable {E : Type} {R : Type} [ResourceAlgebra R]

/-- A generic consequence: combining with the empty residue on the left does not
    change the measured grade.  (Holds for *any* resource algebra, by
    `measure_empty` + `measure_combine` + `one_mul`.) -/
theorem measure_combine_empty_left (rm : ResidueMeasure E R) (e : E) :
    rm.measure (rm.combine rm.empty e) = rm.measure e := by
  rw [rm.measure_combine, rm.measure_empty]
  exact ResourceSemiring.one_mul (rm.measure e)

/-- Symmetric form: combining with the empty residue on the right. -/
theorem measure_combine_empty_right (rm : ResidueMeasure E R) (e : E) :
    rm.measure (rm.combine e rm.empty) = rm.measure e := by
  rw [rm.measure_combine, rm.measure_empty]
  exact ResourceSemiring.mul_one (rm.measure e)

end ResidueMeasure

-- ── A concrete, inhabited bridge (proves the direction is real and usable) ────
-- Echo residues are modelled here as a `List Unit` (an opaque bag of residue
-- events — NOT a resource algebra).  They are measured into the *max-plus* cost
-- algebra by event count, accumulating sequentially (`⊠ = +`).  This compiles, so
-- the `E → R` direction is genuinely populated; `List Unit` never becomes a
-- `ResourceAlgebra`.

/-- A worked residue measure: count residue events into the max-plus algebra. -/
def echoResidueAsMaxPlusCost :
    ResidueMeasure (List Unit) Instances.MaxPlus.Carrier where
  combine := List.append
  empty   := []
  measure := fun l => .val l.length
  measure_empty   := rfl
  measure_combine := by
    intro e₁ e₂
    show Hyperpolymath.Tropical.Tropical.val (e₁ ++ e₂).length
        = Hyperpolymath.Tropical.tMul _ _
    simp [Hyperpolymath.Tropical.tMul, List.length_append]

end Resource
