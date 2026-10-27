-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
import Resource.Algebra.ParametricLaws
import Resource.Instances.MaxPlus
import Resource.Instances.MinPlus
import Resource.Instances.MinMax

/-!
  # Tropical as an infinite-carrier stress test

  Author: Jonathan D.A. Jewell (hyperpolymath)
  Verified: Lean 4.35.0 (pinned via `lean-toolchain`), no Mathlib.

  The finite usage instances (`Linear`, `Affine`) have three-element carriers, so
  one *could* discharge their laws by brute enumeration.  The tropical instances
  cannot be handled that way: their carriers are **infinite**.  This module makes
  that precise and machine-checks it.

  This is the load-bearing honesty check on the whole abstraction.  If the
  resource-algebra interface only ever had to cope with `{0,1,ω}`, "ordered
  semiring" would be over-engineering — a finite lookup table would do.  Because
  the *same* interface and the *same* `parametric_resource_transport` theorem also
  instantiate at the infinite max-plus, min-plus, and min-max carriers (see the
  `#check`s below), the abstraction is doing real work: it is not a finite
  `{0,1,ω}` reification in disguise.

  Recall too that `parametric_resource_transport` and everything in
  `Resource.Algebra.Dioid` is proved **without any case split on the carrier** —
  which is exactly why it survives the move to an infinite carrier.
-/

namespace Resource

/-- A carrier is infinite if `ℕ` injects into it.  The injectivity condition is
    inlined (both `Mathlib`'s `Infinite` class and core `Function.Injective` are
    unavailable under the pinned, dependency-free `import Init` toolchain). -/
def Infinite (T : Type) : Prop := ∃ f : Nat → T, ∀ a b, f a = f b → a = b

namespace Instances

/-- The max-plus carrier `ℕ ∪ {−∞}` is infinite: `val : ℕ → Tropical` injects. -/
theorem infinite_maxPlus : Resource.Infinite MaxPlus.Carrier := by
  refine ⟨Hyperpolymath.Tropical.Tropical.val, ?_⟩
  intro a b h; injection h

/-- The min-plus carrier `ℕ ∪ {+∞}` is infinite. -/
theorem infinite_minPlus : Resource.Infinite MinPlus.Carrier := by
  refine ⟨MinPlus.MinPlus.val, ?_⟩
  intro a b h; injection h

/-- The min-max / bottleneck carrier `ℕ ∪ {+∞}` is infinite. -/
theorem infinite_minMax : Resource.Infinite MinMax.Carrier := by
  refine ⟨MinMax.MinMax.val, ?_⟩
  intro a b h; injection h

end Instances

-- ── The abstraction transports to the infinite carriers ──────────────────────
-- The single generic theorem `parametric_resource_transport` instantiates at
-- every infinite tropical carrier with no extra proof.  That is the payoff: a
-- downstream soundness proof parametric over `[ResourceAlgebra R]` is reusable at
-- these infinite algebras precisely because the proof never enumerated a carrier.

example : ConsumerLawBundle Instances.MaxPlus.Carrier := parametric_resource_transport _
example : ConsumerLawBundle Instances.MinPlus.Carrier := parametric_resource_transport _
example : ConsumerLawBundle Instances.MinMax.Carrier := parametric_resource_transport _

end Resource
