-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
import Resource.Algebra.Dioid

/-!
  # Resource instance — the min-max / bottleneck tropical algebra

  Author: Jonathan D.A. Jewell (hyperpolymath)
  Verified: Lean 4.35.0 (pinned via `lean-toolchain`), no Mathlib.

  The **min-max** (a.k.a. *bottleneck*) tropical semiring on `ℕ ∪ {+∞}`:
  choose the better route (`min`), and compose by the worst step (`max`).  This
  is the clean, honestly-infinite-carrier counterpart of the bottleneck algebra
  in `TropicalAdapterPath.lean` (which models `+∞` with a concrete `1000000`
  bound for proof accessibility); here `top` is a genuine extra constructor.

  ## Tropical conventions (min-max / bottleneck)

  | role                              | here          |
  | --------------------------------- | ------------- |
  | alternative / choice  `⊞` (`add`) | `min`         |
  | sequential composition `⊠` (`mul`)| `max`         |
  | additive zero  `zero`             | `top` (`+∞`)  |
  | multiplicative one `one`          | `val 0`       |

  * **Choice** takes the `min`: pick the route with the lower bottleneck.
  * **Sequential composition** takes the `max`: a composed route is only as good
    as its worst (bottleneck) step.
  * `zero = top = +∞` is the identity of `min` (the "no route" grade) and is also
    absorbing for `max`; `one = val 0` is the identity of `max`.
  * Order direction: `a ⊑ b` is the canonical dioid order `a ⊞ b = b`.  As in
    `MinPlus`, the choice operation is `min`, so the order is the **reverse** of
    numeric `≤`: `val m ⊑ val n ⇔ n ≤ m` (`le_val_val`).  The least element is
    `zero = +∞` (the worst / unreachable); **smaller numeric bottleneck is
    "better" and sits higher in `⊑`**.  This is exactly the order under which
    `TropicalAdapterPath.hub_ceiling` ("one hub caps fidelity") is monotone.
-/

namespace Resource.Instances.MinMax

open scoped Resource.ResourceSemiring

/-- The min-max carrier: a finite bottleneck `val n`, or `top = +∞`. -/
inductive MinMax where
  | val : Nat → MinMax
  | top : MinMax
  deriving DecidableEq, Repr

/-- The carrier, under a stable name. -/
abbrev Carrier : Type := MinMax

namespace MinMax

/-- Choice: the route with the lower bottleneck.  `top = +∞` is neutral. -/
def add : MinMax → MinMax → MinMax
  | .top,   b      => b
  | a,      .top   => a
  | .val m, .val n => .val (Nat.min m n)

/-- Sequential composition: the worse (bottleneck) step.  `top = +∞` absorbs. -/
def mul : MinMax → MinMax → MinMax
  | .top,   _      => .top
  | _,      .top   => .top
  | .val m, .val n => .val (Nat.max m n)

-- ── ℕ helper: `max` distributes over `min` on the right. ─────────────────────

private theorem nat_max_min_distrib_right (a b c : Nat) :
    Nat.max (Nat.min a b) c = Nat.min (Nat.max a c) (Nat.max b c) := by
  simp [Nat.max_comm _ c, Nat.max_min_distrib_left]

/-- `min` is idempotent — min-max is a dioid. -/
theorem add_idem (a : MinMax) : add a a = a := by
  cases a <;> simp [add, Nat.min_self]

def semiring : Resource.ResourceSemiring MinMax where
  zero := .top
  one  := .val 0
  add  := add
  mul  := mul
  add_assoc     := by intro a b c; cases a <;> cases b <;> cases c <;> simp [add, Nat.min_assoc]
  add_comm      := by intro a b;   cases a <;> cases b <;> simp [add, Nat.min_comm]
  zero_add      := by intro a;     cases a <;> rfl
  add_zero      := by intro a;     cases a <;> rfl
  mul_assoc     := by intro a b c; cases a <;> cases b <;> cases c <;> simp [mul, Nat.max_assoc]
  one_mul       := by intro a;     cases a <;> simp [mul]
  mul_one       := by intro a;     cases a <;> simp [mul]
  zero_mul      := by intro a;     cases a <;> rfl
  mul_zero      := by intro a;     cases a <;> rfl
  left_distrib  := by intro a b c; cases a <;> cases b <;> cases c <;> simp [mul, add, Nat.max_min_distrib_left]
  right_distrib := by intro a b c; cases a <;> cases b <;> cases c <;> simp [mul, add, nat_max_min_distrib_right]

instance instResourceAlgebra : Resource.ResourceAlgebra MinMax :=
  Resource.ResourceAlgebra.ofIdempotentAdd (inst := semiring) add_idem

instance : Resource.PartialOrderedResourceAlgebra MinMax :=
  Resource.PartialOrderedResourceAlgebra.ofIdempotentAdd (inst := semiring) add_idem

-- ── The canonical order spelled out (documentation / sanity) ──────────────────

/-- `top = +∞` is the **least** grade (worst / unreachable bottleneck). -/
theorem top_le (a : MinMax) : Resource.ResourceAlgebra.le .top a := by
  show add .top a = a
  cases a <;> rfl

/-- The canonical order is the **reverse** of numeric `≤` on finite grades:
    `val m ⊑ val n ⇔ n ≤ m` (a lower bottleneck is "better", hence higher). -/
theorem le_val_val (m n : Nat) :
    Resource.ResourceAlgebra.le (MinMax.val m) (MinMax.val n) ↔ n ≤ m := by
  show add (MinMax.val m) (MinMax.val n) = MinMax.val n ↔ n ≤ m
  simp only [add, MinMax.val.injEq, Nat.min_def]
  constructor
  · intro h; split at h <;> omega
  · intro h; split <;> omega

-- Smoke tests.
example : Resource.ResourceAlgebra MinMax := inferInstance
example : add (.val 2) (.val 5) = .val 2 := by decide   -- choice: lower bottleneck
example : mul (.val 2) (.val 5) = .val 5 := by decide   -- compose: worst step
example : Resource.ResourceAlgebra.le (MinMax.val 5) (MinMax.val 2) :=
  (le_val_val 5 2).mpr (by omega)

end MinMax
end Resource.Instances.MinMax
