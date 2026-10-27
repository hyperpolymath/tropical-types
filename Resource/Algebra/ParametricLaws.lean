-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
import Resource.Algebra.Ordered

/-!
  # Resource Algebra — parametric laws and the consumer transport theorem

  Author: Jonathan D.A. Jewell (hyperpolymath)
  Verified: Lean 4.35.0 (pinned via `lean-toolchain`), no Mathlib.

  This module exports the **law bundle that downstream soundness proofs depend
  on**, derived once and for all from the `ResourceAlgebra` interface.

  The headline is `parametric_resource_transport` (alias
  `resource_laws_sufficient_for_consumers`):

      theorem parametric_resource_transport (R) [ResourceAlgebra R] :
        ConsumerLawBundle R

  Its content: *any* downstream language whose resource-typing soundness proof
  uses only the `ResourceAlgebra` interface obtains, for free, the full bundle of
  algebraic and order facts it needs — and can therefore be instantiated at
  `Resource.Instances.Linear`, `Affine`, `MaxPlus`, `MinPlus`, or `MinMax`
  without re-proving a single algebraic lemma.

  **Every theorem here is proved abstractly from the interface axioms** — no
  `cases`/`decide` on a carrier, no concrete quantity type.  That is exactly what
  makes the bundle transportable to the infinite tropical carriers.
-/

namespace Resource

open scoped ResourceSemiring ResourceAlgebra

variable {R : Type u} [ResourceAlgebra R]

-- ============================================================================
-- 1.  Derived monotonicity lemmas (abstract — no carrier case-split)
-- ============================================================================

/-- `add` is monotone in its **left** argument, derived from right-monotonicity
    and commutativity. -/
theorem add_le_add_right {a b : R} (h : a ⊑ b) (c : R) : (a ⊞ c) ⊑ (b ⊞ c) := by
  rw [ResourceSemiring.add_comm a c, ResourceSemiring.add_comm b c]
  exact ResourceAlgebra.add_le_add_left a b h c

/-- Two-sided monotonicity of `add`: refining both summands refines the sum. -/
theorem add_le_add {a b c d : R} (h₁ : a ⊑ b) (h₂ : c ⊑ d) :
    (a ⊞ c) ⊑ (b ⊞ d) :=
  ResourceAlgebra.le_trans _ _ _
    (add_le_add_right h₁ c)
    (ResourceAlgebra.add_le_add_left c d h₂ b)

/-- Two-sided monotonicity of `mul`: refining both factors refines the product.
    This is the key "subsumption is preserved by sequential composition" fact a
    resource-typing soundness proof leans on. -/
theorem mul_le_mul {a b c d : R} (h₁ : a ⊑ b) (h₂ : c ⊑ d) :
    (a ⊠ c) ⊑ (b ⊠ d) :=
  ResourceAlgebra.le_trans _ _ _
    (ResourceAlgebra.mul_le_mul_right a b h₁ c)
    (ResourceAlgebra.mul_le_mul_left c d h₂ b)

-- ============================================================================
-- 2.  The consumer law bundle
-- ============================================================================

/-- **The downstream-consumer contract.**

    Everything a generic quantitative / resource type system needs about its
    grade algebra, in one record: the semiring laws, the preorder laws, and
    both one- and two-sided monotonicity.  A downstream soundness proof that is
    parametric over `[ResourceAlgebra R]` may quote exactly these facts; it never
    needs to inspect the concrete carrier.

    Deliberately a `Prop` (all fields are propositions), so it composes like
    `And` and carries no data. -/
structure ConsumerLawBundle (R : Type u) [ResourceAlgebra R] : Prop where
  /-- `add` associativity. -/
  add_assoc     : ∀ a b c : R, (a ⊞ b) ⊞ c = a ⊞ (b ⊞ c)
  /-- `add` commutativity. -/
  add_comm      : ∀ a b : R, a ⊞ b = b ⊞ a
  /-- `zero` is the left identity of `add`. -/
  zero_add      : ∀ a : R, (ResourceSemiring.zero : R) ⊞ a = a
  /-- `zero` is the right identity of `add`. -/
  add_zero      : ∀ a : R, a ⊞ (ResourceSemiring.zero : R) = a
  /-- `mul` associativity. -/
  mul_assoc     : ∀ a b c : R, (a ⊠ b) ⊠ c = a ⊠ (b ⊠ c)
  /-- `one` is the left identity of `mul`. -/
  one_mul       : ∀ a : R, (ResourceSemiring.one : R) ⊠ a = a
  /-- `one` is the right identity of `mul`. -/
  mul_one       : ∀ a : R, a ⊠ (ResourceSemiring.one : R) = a
  /-- `zero` annihilates on the left. -/
  zero_mul      : ∀ a : R, (ResourceSemiring.zero : R) ⊠ a = (ResourceSemiring.zero : R)
  /-- `zero` annihilates on the right. -/
  mul_zero      : ∀ a : R, a ⊠ (ResourceSemiring.zero : R) = (ResourceSemiring.zero : R)
  /-- Left distributivity. -/
  left_distrib  : ∀ a b c : R, a ⊠ (b ⊞ c) = (a ⊠ b) ⊞ (a ⊠ c)
  /-- Right distributivity. -/
  right_distrib : ∀ a b c : R, (a ⊞ b) ⊠ c = (a ⊠ c) ⊞ (b ⊠ c)
  /-- `⊑` is reflexive. -/
  le_refl       : ∀ a : R, a ⊑ a
  /-- `⊑` is transitive. -/
  le_trans      : ∀ a b c : R, a ⊑ b → b ⊑ c → a ⊑ c
  /-- Two-sided monotonicity of `add`. -/
  add_le_add    : ∀ a b c d : R, a ⊑ b → c ⊑ d → (a ⊞ c) ⊑ (b ⊞ d)
  /-- Two-sided monotonicity of `mul`. -/
  mul_le_mul    : ∀ a b c d : R, a ⊑ b → c ⊑ d → (a ⊠ c) ⊑ (b ⊠ d)
  /-- Left-argument monotonicity of `add`. -/
  add_le_add_left  : ∀ a b : R, a ⊑ b → ∀ c : R, (c ⊞ a) ⊑ (c ⊞ b)
  /-- Right-argument monotonicity of `add`. -/
  add_le_add_right : ∀ a b : R, a ⊑ b → ∀ c : R, (a ⊞ c) ⊑ (b ⊞ c)
  /-- Left-argument monotonicity of `mul`. -/
  mul_le_mul_left  : ∀ a b : R, a ⊑ b → ∀ c : R, (c ⊠ a) ⊑ (c ⊠ b)
  /-- Right-argument monotonicity of `mul`. -/
  mul_le_mul_right : ∀ a b : R, a ⊑ b → ∀ c : R, (a ⊠ c) ⊑ (b ⊠ c)

/-- A stable, intention-revealing alias for `ConsumerLawBundle`, matching the
    name used in the foundation contract / downstream documentation. -/
abbrev GenericResourceTypingLaws (R : Type u) [ResourceAlgebra R] : Prop :=
  ConsumerLawBundle R

-- ============================================================================
-- 3.  The transport theorem
-- ============================================================================

/-- **Parametric resource transport.**

    For *every* resource algebra `R`, the consumer law bundle holds.  This is the
    single fact `tropical-resource-typing` exports to downstream languages: prove
    your resource soundness parametrically over `[ResourceAlgebra R]`, quote
    `ConsumerLawBundle`, and instantiate at any concrete algebra.

    Proved entirely from the interface — it transports to the infinite tropical
    carriers exactly because it never looks at the carrier. -/
theorem parametric_resource_transport (R : Type u) [ResourceAlgebra R] :
    ConsumerLawBundle R where
  add_assoc        := ResourceSemiring.add_assoc
  add_comm         := ResourceSemiring.add_comm
  zero_add         := ResourceSemiring.zero_add
  add_zero         := ResourceSemiring.add_zero
  mul_assoc        := ResourceSemiring.mul_assoc
  one_mul          := ResourceSemiring.one_mul
  mul_one          := ResourceSemiring.mul_one
  zero_mul         := ResourceSemiring.zero_mul
  mul_zero         := ResourceSemiring.mul_zero
  left_distrib     := ResourceSemiring.left_distrib
  right_distrib    := ResourceSemiring.right_distrib
  le_refl          := ResourceAlgebra.le_refl
  le_trans         := ResourceAlgebra.le_trans
  add_le_add       := fun _ _ _ _ h₁ h₂ => add_le_add h₁ h₂
  mul_le_mul       := fun _ _ _ _ h₁ h₂ => mul_le_mul h₁ h₂
  add_le_add_left  := ResourceAlgebra.add_le_add_left
  add_le_add_right := fun a b h c => add_le_add_right (a := a) (b := b) h c
  mul_le_mul_left  := ResourceAlgebra.mul_le_mul_left
  mul_le_mul_right := ResourceAlgebra.mul_le_mul_right

/-- Alias of `parametric_resource_transport` under the contract-document name:
    the resource-algebra laws are sufficient for downstream consumers. -/
theorem resource_laws_sufficient_for_consumers (R : Type u) [ResourceAlgebra R] :
    ConsumerLawBundle R :=
  parametric_resource_transport R

end Resource
