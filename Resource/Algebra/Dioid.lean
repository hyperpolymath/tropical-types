-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
import Resource.Algebra.Ordered

/-!
  # Resource Algebra — the canonical dioid order builder

  Author: Jonathan D.A. Jewell (hyperpolymath)
  Verified: Lean 4.35.0 (pinned via `lean-toolchain`), no Mathlib.

  A **dioid** is a semiring whose addition is idempotent (`a ⊞ a = a`).  Every
  dioid carries a *canonical* order

      a ⊑ b   ⇔   a ⊞ b = b

  and — crucially — **all** the `ResourceAlgebra` order laws (reflexivity,
  transitivity, antisymmetry, and monotonicity of both operations) follow purely
  algebraically from the semiring laws plus idempotence.  No case analysis on the
  carrier is used anywhere in this file, so the construction applies verbatim to
  the *infinite* tropical carriers.

  The tropical resource instances (`MaxPlus`, `MinPlus`, `MinMax`) are built with
  these helpers: each supplies its `ResourceSemiring` and a one-line idempotence
  proof, and inherits the entire ordered structure.  This is also the precise,
  machine-checked statement that the tropical order *is* the order induced by the
  algebra — not an ad-hoc numeric comparison bolted on the side.
-/

namespace Resource

open scoped ResourceSemiring

variable {R : Type u} [ResourceSemiring R]

/-- The canonical order of a dioid: `a ⊑ b` iff `a ⊞ b = b`. -/
def canonicalLe (a b : R) : Prop := a ⊞ b = b

theorem canonicalLe_refl (idem : ∀ a : R, a ⊞ a = a) (a : R) : canonicalLe a a :=
  idem a

theorem canonicalLe_trans (a b c : R)
    (hab : canonicalLe a b) (hbc : canonicalLe b c) : canonicalLe a c := by
  simp only [canonicalLe] at hab hbc ⊢
  calc a ⊞ c = a ⊞ (b ⊞ c)   := by rw [hbc]
    _ = (a ⊞ b) ⊞ c           := by rw [← ResourceSemiring.add_assoc]
    _ = b ⊞ c                 := by rw [hab]
    _ = c                     := hbc

theorem canonicalLe_antisymm (a b : R)
    (hab : canonicalLe a b) (hba : canonicalLe b a) : a = b := by
  simp only [canonicalLe] at hab hba
  rw [← hab, ResourceSemiring.add_comm a b, hba]

theorem canonicalLe_add_le_add_left (idem : ∀ a : R, a ⊞ a = a)
    (a b : R) (h : canonicalLe a b) (c : R) :
    canonicalLe (c ⊞ a) (c ⊞ b) := by
  simp only [canonicalLe] at h ⊢
  calc (c ⊞ a) ⊞ (c ⊞ b)
      = c ⊞ (a ⊞ (c ⊞ b)) := by rw [ResourceSemiring.add_assoc]
    _ = c ⊞ ((a ⊞ c) ⊞ b) := by rw [← ResourceSemiring.add_assoc a c b]
    _ = c ⊞ ((c ⊞ a) ⊞ b) := by rw [ResourceSemiring.add_comm a c]
    _ = c ⊞ (c ⊞ (a ⊞ b)) := by rw [ResourceSemiring.add_assoc c a b]
    _ = (c ⊞ c) ⊞ (a ⊞ b) := by rw [← ResourceSemiring.add_assoc]
    _ = c ⊞ (a ⊞ b)       := by rw [idem]
    _ = c ⊞ b             := by rw [h]

theorem canonicalLe_mul_le_mul_left (a b : R) (h : canonicalLe a b) (c : R) :
    canonicalLe (c ⊠ a) (c ⊠ b) := by
  simp only [canonicalLe] at h ⊢
  calc (c ⊠ a) ⊞ (c ⊠ b)
      = c ⊠ (a ⊞ b) := (ResourceSemiring.left_distrib c a b).symm
    _ = c ⊠ b       := by rw [h]

theorem canonicalLe_mul_le_mul_right (a b : R) (h : canonicalLe a b) (c : R) :
    canonicalLe (a ⊠ c) (b ⊠ c) := by
  simp only [canonicalLe] at h ⊢
  calc (a ⊠ c) ⊞ (b ⊠ c)
      = (a ⊞ b) ⊠ c := (ResourceSemiring.right_distrib a b c).symm
    _ = b ⊠ c       := by rw [h]

/-- Build a `ResourceAlgebra` from any **idempotent** resource semiring, using
    the canonical order `a ⊑ b ⇔ a ⊞ b = b`.  All order/monotonicity laws are
    discharged generically — the instance supplies only idempotence. -/
def ResourceAlgebra.ofIdempotentAdd [inst : ResourceSemiring R]
    (idem : ∀ a : R, a ⊞ a = a) : ResourceAlgebra R where
  toResourceSemiring := inst
  le               := canonicalLe
  le_refl          := canonicalLe_refl idem
  le_trans         := canonicalLe_trans
  add_le_add_left  := fun a b h c => canonicalLe_add_le_add_left idem a b h c
  mul_le_mul_left  := canonicalLe_mul_le_mul_left
  mul_le_mul_right := canonicalLe_mul_le_mul_right

/-- As `ofIdempotentAdd`, but additionally records that the canonical order is a
    genuine **partial order** (antisymmetric).  Every dioid order is. -/
def PartialOrderedResourceAlgebra.ofIdempotentAdd [inst : ResourceSemiring R]
    (idem : ∀ a : R, a ⊞ a = a) : PartialOrderedResourceAlgebra R where
  toResourceAlgebra := ResourceAlgebra.ofIdempotentAdd (inst := inst) idem
  le_antisymm := canonicalLe_antisymm

end Resource
