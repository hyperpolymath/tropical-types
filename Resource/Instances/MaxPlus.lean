-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
import Resource.Algebra.Dioid
import TropicalSessionTypes

/-!
  # Resource instance — the max-plus tropical cost algebra

  Author: Jonathan D.A. Jewell (hyperpolymath)
  Verified: Lean 4.35.0 (pinned via `lean-toolchain`), no Mathlib.

  This instance **re-exports**, rather than duplicates, the max-plus semiring
  already proved in `TropicalSessionTypes.lean` (`Hyperpolymath.Tropical`,
  carrier `Tropical = val ℕ | bot`).  It wires those thirteen law theorems into a
  `Resource.ResourceSemiring`, then obtains the full ordered `ResourceAlgebra`
  from the canonical dioid-order builder — `add` (`max`) is idempotent, so the
  order and monotonicity come for free and algebraically (`Resource.Algebra.Dioid`).

  ## Tropical conventions (max-plus)

  | role                              | here          |
  | --------------------------------- | ------------- |
  | alternative / choice  `⊞` (`add`) | `max`         |
  | sequential composition `⊠` (`mul`)| `+` (ℕ-add)   |
  | additive zero  `zero`             | `bot` (`−∞`)  |
  | multiplicative one `one`          | `val 0`       |

  * **Choice** of two branches takes the `max`: the cost of a speculative /
    parallel choice is the worst (bottleneck) branch, not the sum.
  * **Sequential composition** adds costs (`val m ⊠ val n = val (m + n)`).
  * `zero = bot = −∞` is the identity of `max` (the "no alternative" grade);
    `one = val 0` is the identity of `+` (the "free" grade).
  * Order direction: `a ⊑ b` is the canonical dioid order `a ⊞ b = b`, which here
    is the **numeric `≤`** with `bot` (`−∞`) least.  Smaller grade = **cheaper /
    less costly / better**; `a ⊑ b` reads "`a` costs no more than `b`".

  The carrier is **infinite** (`val : ℕ → Tropical` is an injection) — see
  `Resource.Stress`.  Idempotence of `max` makes this a dioid; non-idempotent
  `{0,1,ω}` usage instances live in `Resource.Instances.{Linear,Affine}`.
-/

namespace Resource.Instances.MaxPlus

open Hyperpolymath.Tropical
open scoped Resource.ResourceSemiring

/-- The max-plus carrier (re-export of `Hyperpolymath.Tropical.Tropical`). -/
abbrev Carrier : Type := Tropical

/-- The max-plus resource semiring: the thirteen laws proved in
    `TropicalSessionTypes.lean`, repackaged behind the consumer interface. -/
def semiring : Resource.ResourceSemiring Tropical where
  zero := .bot
  one  := .val 0
  add  := tAdd
  mul  := tMul
  add_assoc     := add_assoc_trop
  add_comm      := add_comm_trop
  zero_add      := bot_add
  add_zero      := add_bot
  mul_assoc     := mul_assoc_trop
  one_mul       := one_mul_trop
  mul_one       := mul_one_trop
  zero_mul      := bot_mul
  mul_zero      := mul_bot
  left_distrib  := left_distrib_trop
  right_distrib := right_distrib_trop

/-- `max` is idempotent — this is what makes max-plus a dioid. -/
theorem tAdd_idem (a : Tropical) : tAdd a a = a := by
  cases a with
  | bot   => rfl
  | val n => simp [tAdd, Nat.max_self]

instance instResourceAlgebra : Resource.ResourceAlgebra Tropical :=
  Resource.ResourceAlgebra.ofIdempotentAdd (inst := semiring) tAdd_idem

instance : Resource.PartialOrderedResourceAlgebra Tropical :=
  Resource.PartialOrderedResourceAlgebra.ofIdempotentAdd (inst := semiring) tAdd_idem

-- ── The canonical order spelled out (documentation / sanity) ──────────────────

/-- `bot` (`−∞`) is the least grade: the cheapest, the identity of choice.
    (`ResourceAlgebra.le .bot a` is, by the canonical order, `tAdd .bot a = a`.) -/
theorem bot_le (a : Tropical) : Resource.ResourceAlgebra.le .bot a := bot_add a

/-- On finite grades the canonical order is exactly the numeric `≤`. -/
theorem le_val_val (m n : Nat) :
    Resource.ResourceAlgebra.le (Tropical.val m) (Tropical.val n) ↔ m ≤ n := by
  show tAdd (Tropical.val m) (Tropical.val n) = Tropical.val n ↔ m ≤ n
  simp only [tAdd, Tropical.val.injEq, Nat.max_def]
  constructor
  · intro h; split at h <;> omega
  · intro h; split <;> omega

-- Smoke tests.
example : Resource.ResourceAlgebra Tropical := inferInstance
example : tAdd (.val 2) (.val 5) = .val 5 := by decide   -- choice: worst branch
example : tMul (.val 2) (.val 5) = .val 7 := by decide   -- sequential: sum
example : Resource.ResourceAlgebra.le (Tropical.val 2) (Tropical.val 5) :=
  (le_val_val 2 5).mpr (by omega)

end Resource.Instances.MaxPlus
