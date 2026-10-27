-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
import Init

/-!
  # Resource Algebra — the consumer-facing interface (algebra layer)

  Author: Jonathan D.A. Jewell (hyperpolymath)
  Verified: Lean 4.35.0 (pinned via `lean-toolchain`), `import Init` (no Mathlib).

  ## What this module is

  This is the **stable, consumer-facing resource-algebra interface** that
  `tropical-resource-typing` exports for downstream languages such as `my-lang`.

  A *resource grade* is a binder/resource quantity: usage, cost, latency,
  critical path, bottleneck, residue measure, etc.  A *resource algebra* is the
  ordered-semiring / usage-algebra interface that resource typing reasons over.
  Concrete *resource instances* — linear `{0,1,ω}`, affine `{0,1,ω}`, max-plus,
  min-plus, min-max — all satisfy this one interface, so a downstream soundness
  proof written against the interface can be instantiated at any of them without
  re-proving algebraic facts.

  ## Design rationale (read before changing)

  * **Operations are bundled as fields**, not via core `Add`/`Mul`/`Zero`/`One`
    typeclasses.  Lean 4.13.0 core ships `Zero` but not `One`, and the existing
    `TropicalSessionTypes.lean` already defines its own local `One` plus a global
    `OfNat _ 1` bridge.  Bundling the ops as fields keeps this interface fully
    self-contained and free of any notation/`One`-instance collision, while
    staying Mathlib-free.
  * The laws here are **only the algebra**: associativity, identities,
    distributivity, and annihilation.  The order, the preorder laws, and
    monotonicity live one layer up in `Resource.Algebra.Ordered`, so a consumer
    that needs only the algebraic skeleton can depend on this module alone.
  * Deliberately **NOT** required: a finite carrier, additive idempotence,
    non-idempotence, multiplicative commutativity, totality, or decidable
    equality.  Tropical instances are idempotent and have infinite carriers;
    `{0,1,ω}` usage instances are non-idempotent and finite; both must fit the
    same interface, so none of those properties may be baked in here.
-/

namespace Resource

/-- A (not necessarily commutative) **resource semiring**: the algebraic core of
    a resource grade.

    Intended reading of the two operations for a resource consumer:

    * `add` (`⊞`)  — combine *alternative* demands / choose between branches.
      In a dioid (tropical) instance this is idempotent; in a `{0,1,ω}` usage
      instance it is not.  The interface assumes neither.
    * `mul` (`⊠`)  — *sequential* composition / accumulation of demands.
      Not assumed commutative: sequential composition need not commute.

    `zero` is the additive identity (and multiplicative annihilator); `one` is
    the multiplicative identity. -/
class ResourceSemiring (R : Type u) where
  zero : R
  one  : R
  add  : R → R → R
  mul  : R → R → R
  /-- `add` is associative. -/
  add_assoc     : ∀ a b c : R, add (add a b) c = add a (add b c)
  /-- `add` is commutative (combining demands is order-independent). -/
  add_comm      : ∀ a b : R, add a b = add b a
  /-- `zero` is the left identity of `add`. -/
  zero_add      : ∀ a : R, add zero a = a
  /-- `zero` is the right identity of `add`. -/
  add_zero      : ∀ a : R, add a zero = a
  /-- `mul` is associative. -/
  mul_assoc     : ∀ a b c : R, mul (mul a b) c = mul a (mul b c)
  /-- `one` is the left identity of `mul`. -/
  one_mul       : ∀ a : R, mul one a = a
  /-- `one` is the right identity of `mul`. -/
  mul_one       : ∀ a : R, mul a one = a
  /-- `zero` annihilates on the left under `mul`. -/
  zero_mul      : ∀ a : R, mul zero a = zero
  /-- `zero` annihilates on the right under `mul`. -/
  mul_zero      : ∀ a : R, mul a zero = zero
  /-- `mul` distributes over `add` on the left. -/
  left_distrib  : ∀ a b c : R, mul a (add b c) = add (mul a b) (mul a c)
  /-- `mul` distributes over `add` on the right. -/
  right_distrib : ∀ a b c : R, mul (add a b) c = add (mul a c) (mul b c)

namespace ResourceSemiring

-- NOTE on glyph choice: core Lean's `Init` already binds `⊕` to `Sum` (and
-- `×` to `Prod`).  Using `⊕`/`⊗` here creates an ambiguous-notation hazard, so
-- the resource operations use `⊞` (boxplus) and `⊠` (boxtimes), which core does
-- not claim.

/-- Choice / alternative combination of resource grades. -/
scoped infixl:65 " ⊞ " => ResourceSemiring.add
/-- Sequential composition / accumulation of resource grades. -/
scoped infixl:70 " ⊠ " => ResourceSemiring.mul

end ResourceSemiring

/-- Some consumers want an explicitly **commutative** resource semiring (e.g. a
    cost model where sequential order genuinely does not matter).  This is an
    optional refinement; the core interface does not assume it. -/
class CommResourceSemiring (R : Type u) extends ResourceSemiring R where
  /-- `mul` is commutative. -/
  mul_comm : ∀ a b : R, mul a b = mul b a

end Resource
