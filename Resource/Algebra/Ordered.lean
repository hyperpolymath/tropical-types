-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
import Resource.Algebra.Interface

/-!
  # Resource Algebra — the ordered layer

  Author: Jonathan D.A. Jewell (hyperpolymath)
  Verified: Lean 4.35.0 (pinned via `lean-toolchain`), no Mathlib.

  `ResourceAlgebra R` is the full consumer-facing interface: a
  `ResourceSemiring` (algebra core) together with an order `le` (`⊑`) and the
  laws a generic resource-typing soundness proof actually depends on —

  * the order is a **preorder** (reflexive, transitive), the weakest order that
    supports subsumption / subtyping of resource grades;
  * both operations are **monotone** with respect to that order, so refining a
    grade refines every composite that uses it.

  Antisymmetry is *not* part of the core (a preorder is enough for subsumption);
  instances that have it expose the optional `PartialOrderedResourceAlgebra`
  refinement below.  No instance is forced to be a partial order, total, or
  decidable.

  ## Order direction (a per-instance convention, documented at each instance)

  The interface fixes the *laws* of `⊑`, not its *meaning*.  Each concrete
  instance documents which direction of `a ⊑ b` means "better", "worse",
  "less costly", or "more available" for that algebra (see `Resource.Instances.*`).
-/

namespace Resource

open scoped ResourceSemiring

/-- The full **resource algebra**: an ordered resource semiring whose operations
    are monotone.  This is the interface downstream resource typing should be
    parametric over. -/
class ResourceAlgebra (R : Type u) extends ResourceSemiring R where
  /-- The grade order.  `le a b` (written `a ⊑ b`) is read, per instance, as
      "`a` refines / is subsumed by `b`". -/
  le : R → R → Prop
  /-- `⊑` is reflexive. -/
  le_refl  : ∀ a : R, le a a
  /-- `⊑` is transitive. -/
  le_trans : ∀ a b c : R, le a b → le b c → le a c
  /-- `add` is monotone in its right argument (hence, with `add_comm`, in both). -/
  add_le_add_left  : ∀ a b : R, le a b → ∀ c : R, le (c ⊞ a) (c ⊞ b)
  /-- `mul` is monotone in its right argument. -/
  mul_le_mul_left  : ∀ a b : R, le a b → ∀ c : R, le (c ⊠ a) (c ⊠ b)
  /-- `mul` is monotone in its left argument. -/
  mul_le_mul_right : ∀ a b : R, le a b → ∀ c : R, le (a ⊠ c) (b ⊠ c)

namespace ResourceAlgebra

/-- Grade subsumption: `a ⊑ b` is read "`a` refines / is at least as permissive
    as required by `b`", with the precise direction fixed at each instance. -/
scoped infix:50 " ⊑ " => ResourceAlgebra.le

end ResourceAlgebra

/-- Optional refinement: the order is additionally **antisymmetric**, i.e. a
    genuine partial order.  Linear, affine, min-plus and min-max all satisfy
    this; consumers that need it can require this stronger interface, but the
    parametric theory in `Resource.Algebra.ParametricLaws` never does. -/
class PartialOrderedResourceAlgebra (R : Type u) extends ResourceAlgebra R where
  /-- `⊑` is antisymmetric. -/
  le_antisymm : ∀ a b : R, le a b → le b a → a = b

end Resource
