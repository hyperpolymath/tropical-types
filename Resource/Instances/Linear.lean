-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
import Resource.Algebra.ParametricLaws

/-!
  # Resource instance — the linear usage quantity `{0, 1, ω}`

  Author: Jonathan D.A. Jewell (hyperpolymath)
  Verified: Lean 4.35.0 (pinned via `lean-toolchain`), no Mathlib.

  The canonical **linear** (quantitative type theory, à la Atkey 2018) usage
  semiring: a binder is used exactly `0`, exactly `1`, or `ω`-many (unbounded)
  times.  This is a *finite* resource instance — a deliberate contrast with the
  infinite tropical carriers in `Resource.Instances.{MaxPlus,MinPlus,MinMax}`.

  ## Conventions for this instance

  * `add` (`⊞`) — combine two *demands* on the same binder (e.g. both branches of
    a pair use it): `1 ⊞ 1 = ω` (used twice ⇒ unbounded for the linear discipline).
  * `mul` (`⊠`) — *scale* a demand by an outer multiplicity (sequential / nested
    use): `ω ⊠ 1 = ω`, `0 ⊠ x = 0`.
  * `zero = 0` — unused (additive identity, multiplicative annihilator).
  * `one  = 1` — used exactly once (multiplicative identity).
  * Order `a ⊑ b` ("`a` refines `b`") holds iff `a = b` or `b = ω`.  Read: a
    grade is subsumed only by itself or by `ω` (the "use any number of times"
    grade).  `0` and `1` are **incomparable** — that is what makes this the
    *linear* discipline (no weakening `1 ↦ 0`, no contraction).  Contrast
    `Resource.Instances.Affine`, which differs *only* in the order.

  Idempotence is **false** here (`1 ⊞ 1 = ω ≠ 1`); the generic interface never
  assumes it, so this instance and the (idempotent) tropical ones share it.
-/

namespace Resource.Instances

/-- The linear usage quantity: `0` (unused), `1` (used once), `ω` (unbounded). -/
inductive Linear where
  | zero
  | one
  | omega
  deriving DecidableEq, Repr

namespace Linear

/-- Combine two demands. `1 ⊞ 1 = ω`; anything with `ω` is `ω`; `0` is neutral. -/
def add : Linear → Linear → Linear
  | .zero,  b      => b
  | a,      .zero  => a
  | .one,   .one   => .omega
  | .one,   .omega => .omega
  | .omega, .one   => .omega
  | .omega, .omega => .omega

/-- Scale a demand. `0` annihilates; `1` is neutral; `ω ⊠ ω = ω`. -/
def mul : Linear → Linear → Linear
  | .zero,  _      => .zero
  | _,      .zero  => .zero
  | .one,   b      => b
  | a,      .one   => a
  | .omega, .omega => .omega

/-- `a ⊑ b` iff `a = b` or `b = ω`.  `0` and `1` are incomparable: the linear
    discipline forbids weakening, so neither subsumes the other. -/
def le (a b : Linear) : Prop := a = b ∨ b = .omega

-- ── Order facts, proved about the concrete `le`/`add`/`mul` (finite case split
--    is legitimate here: the carrier really is the three-element set). ─────────

theorem le_refl' (a : Linear) : le a a := Or.inl rfl

theorem le_trans' (a b c : Linear) (hab : le a b) (hbc : le b c) : le a c := by
  cases a <;> cases b <;> cases c <;> simp_all [le]

theorem le_antisymm' (a b : Linear) (hab : le a b) (hba : le b a) : a = b := by
  cases a <;> cases b <;> simp_all [le]

theorem add_le_add_left' (a b : Linear) (h : le a b) (c : Linear) :
    le (add c a) (add c b) := by
  cases a <;> cases b <;> cases c <;> simp_all [le, add]

theorem mul_le_mul_left' (a b : Linear) (h : le a b) (c : Linear) :
    le (mul c a) (mul c b) := by
  cases a <;> cases b <;> cases c <;> simp_all [le, mul]

theorem mul_le_mul_right' (a b : Linear) (h : le a b) (c : Linear) :
    le (mul a c) (mul b c) := by
  cases a <;> cases b <;> cases c <;> simp_all [le, mul]

instance instResourceAlgebra : Resource.ResourceAlgebra Linear where
  zero := .zero
  one  := .one
  add  := add
  mul  := mul
  le   := le
  add_assoc     := by intro a b c; cases a <;> cases b <;> cases c <;> rfl
  add_comm      := by intro a b;   cases a <;> cases b <;> rfl
  zero_add      := by intro a;     cases a <;> rfl
  add_zero      := by intro a;     cases a <;> rfl
  mul_assoc     := by intro a b c; cases a <;> cases b <;> cases c <;> rfl
  one_mul       := by intro a;     cases a <;> rfl
  mul_one       := by intro a;     cases a <;> rfl
  zero_mul      := by intro a;     cases a <;> rfl
  mul_zero      := by intro a;     cases a <;> rfl
  left_distrib  := by intro a b c; cases a <;> cases b <;> cases c <;> rfl
  right_distrib := by intro a b c; cases a <;> cases b <;> cases c <;> rfl
  le_refl          := le_refl'
  le_trans         := le_trans'
  add_le_add_left  := add_le_add_left'
  mul_le_mul_left  := mul_le_mul_left'
  mul_le_mul_right := mul_le_mul_right'

instance : Resource.PartialOrderedResourceAlgebra Linear where
  le_antisymm := le_antisymm'

-- Smoke tests: the interface is satisfied and a couple of computations hold.
example : Resource.ResourceAlgebra Linear := inferInstance
example : add .one .one = .omega := rfl
example : mul .zero .omega = .zero := rfl
example : le .one .omega := Or.inr rfl
example : ¬ le .zero .one := by simp [le]

end Linear
end Resource.Instances
