-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
import Resource.Algebra.ParametricLaws
import Resource.Instances.Linear
import Resource.Instances.Affine
import Resource.Instances.MaxPlus
import Resource.Instances.MinPlus
import Resource.Instances.MinMax

/-!
  # Conformance — every instance satisfies the one interface, and a parametric
  #              consumer proof instantiates at all of them

  Author: Jonathan D.A. Jewell (hyperpolymath)
  Verified: Lean 4.35.0 (pinned via `lean-toolchain`), no Mathlib.

  This module is the machine-checked statement of the acceptance criteria:

  * linear, affine, max-plus, min-plus and min-max all satisfy the *same*
    `ResourceAlgebra` interface (the `inferInstance` lines), and the *same*
    `ConsumerLawBundle` (`parametric_resource_transport`);
  * a downstream-style lemma proved **once**, parametric over the interface and
    quoting only the bundle, instantiates at each of the five with no re-proof.

  It is the executable witness that the abstraction is genuinely reusable across
  finite usage grades and infinite tropical grades alike.
-/

namespace Resource.Conformance

open scoped Resource.ResourceSemiring Resource.ResourceAlgebra

/-- A toy "downstream soundness" obligation, proved **once** for every resource
    algebra using nothing but `ConsumerLawBundle`: refining both factors of a
    sequential composition refines the composite (subsumption is preserved by
    `⊠`).  A real consumer's soundness proof has this shape — parametric over the
    interface, then instantiated. -/
theorem subsumption_transports {R : Type u} [Resource.ResourceAlgebra R]
    {a b c d : R} (h₁ : a ⊑ b) (h₂ : c ⊑ d) : (a ⊠ c) ⊑ (b ⊠ d) :=
  (Resource.parametric_resource_transport R).mul_le_mul a b c d h₁ h₂

-- ── Every instance satisfies the interface … ─────────────────────────────────

example : Resource.ResourceAlgebra Resource.Instances.Linear         := inferInstance
example : Resource.ResourceAlgebra Resource.Instances.Affine         := inferInstance
example : Resource.ResourceAlgebra Resource.Instances.MaxPlus.Carrier := inferInstance
example : Resource.ResourceAlgebra Resource.Instances.MinPlus.Carrier := inferInstance
example : Resource.ResourceAlgebra Resource.Instances.MinMax.Carrier  := inferInstance

-- … and the consumer law bundle holds for each …
example : Resource.ConsumerLawBundle Resource.Instances.Linear         := Resource.parametric_resource_transport _
example : Resource.ConsumerLawBundle Resource.Instances.Affine         := Resource.parametric_resource_transport _
example : Resource.ConsumerLawBundle Resource.Instances.MaxPlus.Carrier := Resource.parametric_resource_transport _
example : Resource.ConsumerLawBundle Resource.Instances.MinPlus.Carrier := Resource.parametric_resource_transport _
example : Resource.ConsumerLawBundle Resource.Instances.MinMax.Carrier  := Resource.parametric_resource_transport _

-- … and the one parametric lemma instantiates at each (the acceptance criterion).
section Instantiations
open Resource.Instances

example {a b c d : Linear} (h₁ : a ⊑ b) (h₂ : c ⊑ d) : (a ⊠ c) ⊑ (b ⊠ d) :=
  subsumption_transports h₁ h₂
example {a b c d : Affine} (h₁ : a ⊑ b) (h₂ : c ⊑ d) : (a ⊠ c) ⊑ (b ⊠ d) :=
  subsumption_transports h₁ h₂
example {a b c d : MaxPlus.Carrier} (h₁ : a ⊑ b) (h₂ : c ⊑ d) : (a ⊠ c) ⊑ (b ⊠ d) :=
  subsumption_transports h₁ h₂
example {a b c d : MinPlus.Carrier} (h₁ : a ⊑ b) (h₂ : c ⊑ d) : (a ⊠ c) ⊑ (b ⊠ d) :=
  subsumption_transports h₁ h₂
example {a b c d : MinMax.Carrier} (h₁ : a ⊑ b) (h₂ : c ⊑ d) : (a ⊠ c) ⊑ (b ⊠ d) :=
  subsumption_transports h₁ h₂

end Instantiations

end Resource.Conformance
