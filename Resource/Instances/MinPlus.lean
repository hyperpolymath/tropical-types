-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
import Resource.Algebra.Dioid

/-!
  # Resource instance — the min-plus tropical cost algebra

  Author: Jonathan D.A. Jewell (hyperpolymath)
  Verified: Lean 4.35.0 (pinned via `lean-toolchain`), no Mathlib.

  The classical **min-plus** (shortest-path / Mohri) tropical semiring on
  `ℕ ∪ {+∞}`.  A clean infinite-carrier instance: unlike the bounded `1000000`-
  for-`∞` device in `TropicalAdapterPath.lean`, the top element here is a genuine
  extra constructor, so the carrier is honestly infinite (`Resource.Stress`).

  ## Tropical conventions (min-plus)

  | role                              | here            |
  | --------------------------------- | --------------- |
  | alternative / choice  `⊞` (`add`) | `min`           |
  | sequential composition `⊠` (`mul`)| `+` (ℕ-add)     |
  | additive zero  `zero`             | `top` (`+∞`)    |
  | multiplicative one `one`          | `val 0`         |

  * **Choice** of two branches takes the `min`: the cost of choosing the better
    alternative (shortest of the two).
  * **Sequential composition** adds costs (path concatenation).
  * `zero = top = +∞` is the identity of `min` (the "no path / unreachable"
    grade); `one = val 0` is the identity of `+`.
  * Order direction: `a ⊑ b` is the canonical dioid order `a ⊞ b = b`.  Because
    the choice operation is `min`, that order is the **reverse** of numeric `≤`:
    `a ⊑ b ⇔ n ≤ m` for `a = val m, b = val n` (proved as `le_val_val`).  The
    least element is `zero = +∞` (the most costly / unreachable); **smaller
    numeric cost is "better" and sits higher in `⊑`**.  Read `a ⊑ b` as "`b` is
    no more costly than `a`".  (This additive-identity-is-bottom convention is
    the standard one for idempotent cost semirings and is shared by every dioid
    instance here; max-plus lands on plain numeric `≤` only because its choice
    operation is `max`.)
-/

namespace Resource.Instances.MinPlus

open scoped Resource.ResourceSemiring

/-- The min-plus carrier: a finite cost `val n`, or `top = +∞`. -/
inductive MinPlus where
  | val : Nat → MinPlus
  | top : MinPlus
  deriving DecidableEq, Repr

/-- The carrier, under a stable name. -/
abbrev Carrier : Type := MinPlus

namespace MinPlus

/-- Choice: the cheaper alternative.  `top = +∞` is neutral. -/
def add : MinPlus → MinPlus → MinPlus
  | .top,   b      => b
  | a,      .top   => a
  | .val m, .val n => .val (Nat.min m n)

/-- Sequential composition: costs add.  `top = +∞` is absorbing. -/
def mul : MinPlus → MinPlus → MinPlus
  | .top,   _      => .top
  | _,      .top   => .top
  | .val m, .val n => .val (m + n)

-- ── ℕ helper: addition distributes over `min`. ───────────────────────────────

private theorem nat_add_min_left (k m n : Nat) :
    k + Nat.min m n = Nat.min (k + m) (k + n) := by
  simp only [Nat.min_def]; split <;> split <;> omega

private theorem nat_add_min_right (k m n : Nat) :
    Nat.min m n + k = Nat.min (m + k) (n + k) := by
  simp only [Nat.min_def]; split <;> split <;> omega

/-- `min` is idempotent — min-plus is a dioid. -/
theorem add_idem (a : MinPlus) : add a a = a := by
  cases a <;> simp [add, Nat.min_self]

def semiring : Resource.ResourceSemiring MinPlus where
  zero := .top
  one  := .val 0
  add  := add
  mul  := mul
  add_assoc     := by intro a b c; cases a <;> cases b <;> cases c <;> simp [add, Nat.min_assoc]
  add_comm      := by intro a b;   cases a <;> cases b <;> simp [add, Nat.min_comm]
  zero_add      := by intro a;     cases a <;> rfl
  add_zero      := by intro a;     cases a <;> rfl
  mul_assoc     := by intro a b c; cases a <;> cases b <;> cases c <;> simp [mul, Nat.add_assoc]
  one_mul       := by intro a;     cases a <;> simp [mul]
  mul_one       := by intro a;     cases a <;> simp [mul]
  zero_mul      := by intro a;     cases a <;> rfl
  mul_zero      := by intro a;     cases a <;> rfl
  left_distrib  := by intro a b c; cases a <;> cases b <;> cases c <;> simp only [mul, add, nat_add_min_left]
  right_distrib := by intro a b c; cases a <;> cases b <;> cases c <;> simp only [mul, add, nat_add_min_right]

instance instResourceAlgebra : Resource.ResourceAlgebra MinPlus :=
  Resource.ResourceAlgebra.ofIdempotentAdd (inst := semiring) add_idem

instance : Resource.PartialOrderedResourceAlgebra MinPlus :=
  Resource.PartialOrderedResourceAlgebra.ofIdempotentAdd (inst := semiring) add_idem

-- ── The canonical order spelled out (documentation / sanity) ──────────────────

/-- `top = +∞` is the **least** grade (most costly / unreachable): the identity
    of choice and the bottom of the canonical order. -/
theorem top_le (a : MinPlus) : Resource.ResourceAlgebra.le .top a := by
  show add .top a = a
  cases a <;> rfl

/-- The canonical order is the **reverse** of numeric `≤` on finite grades:
    `val m ⊑ val n ⇔ n ≤ m` (smaller cost is "better", hence higher). -/
theorem le_val_val (m n : Nat) :
    Resource.ResourceAlgebra.le (MinPlus.val m) (MinPlus.val n) ↔ n ≤ m := by
  show add (MinPlus.val m) (MinPlus.val n) = MinPlus.val n ↔ n ≤ m
  simp only [add, MinPlus.val.injEq, Nat.min_def]
  constructor
  · intro h; split at h <;> omega
  · intro h; split <;> omega

-- Smoke tests.
example : Resource.ResourceAlgebra MinPlus := inferInstance
example : add (.val 2) (.val 5) = .val 2 := by decide   -- choice: cheaper branch
example : mul (.val 2) (.val 5) = .val 7 := by decide   -- sequential: sum
example : Resource.ResourceAlgebra.le (MinPlus.val 5) (MinPlus.val 2) :=
  (le_val_val 5 2).mpr (by omega)                        -- cheaper (2) is higher

end MinPlus
end Resource.Instances.MinPlus
