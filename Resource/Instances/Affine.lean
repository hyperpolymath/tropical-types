-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
import Resource.Algebra.ParametricLaws

/-!
  # Resource instance — the affine usage quantity `{0, 1, ω}`

  Author: Jonathan D.A. Jewell (hyperpolymath)
  Verified: Lean 4.35.0 (pinned via `lean-toolchain`), no Mathlib.

  The **affine** usage semiring.  Same carrier and same `add`/`mul` as
  `Resource.Instances.Linear`; the *only* difference is the order.

  ## Conventions for this instance

  * `add`, `mul`, `zero`, `one` — exactly as in `Linear`
    (`1 ⊞ 1 = ω`, `0` annihilates `⊠`, etc.).
  * Order `a ⊑ b` is the **chain** `0 ⊑ 1 ⊑ ω` (with reflexivity).  This is the
    affine discipline: **weakening is allowed**, so a binder demanded `1` time may
    be supplied where `ω` is permitted, and `0` (unused) refines `1`.  Concretely
    `a ⊑ b` iff `rank a ≤ rank b` with `rank : 0 ↦ 0, 1 ↦ 1, ω ↦ 2`.

  The distinction from `Linear` is *purely ordinal*: linear leaves `0` and `1`
  incomparable (no weakening); affine makes the whole carrier a total chain.  That
  both fit the one `ResourceAlgebra` interface — differing only in `le` — is the
  point: downstream soundness proved over the interface is reusable across
  disciplines.
-/

namespace Resource.Instances

/-- The affine usage quantity: `0` (unused), `1` (used at most once), `ω`. -/
inductive Affine where
  | zero
  | one
  | omega
  deriving DecidableEq, Repr

namespace Affine

/-- Combine two demands (same as the linear discipline). -/
def add : Affine → Affine → Affine
  | .zero,  b      => b
  | a,      .zero  => a
  | .one,   .one   => .omega
  | .one,   .omega => .omega
  | .omega, .one   => .omega
  | .omega, .omega => .omega

/-- Scale a demand (same as the linear discipline). -/
def mul : Affine → Affine → Affine
  | .zero,  _      => .zero
  | _,      .zero  => .zero
  | .one,   b      => b
  | a,      .one   => a
  | .omega, .omega => .omega

/-- Ordinal rank: `0 ↦ 0`, `1 ↦ 1`, `ω ↦ 2`. -/
def rank : Affine → Nat
  | .zero  => 0
  | .one   => 1
  | .omega => 2

/-- Affine order: the total chain `0 ⊑ 1 ⊑ ω`.  Weakening is permitted. -/
def le (a b : Affine) : Prop := rank a ≤ rank b

-- ── Order facts (finite case split is legitimate: three-element carrier). ─────

theorem le_refl' (a : Affine) : le a a := Nat.le_refl _

theorem le_trans' (a b c : Affine) (hab : le a b) (hbc : le b c) : le a c :=
  Nat.le_trans hab hbc

theorem le_antisymm' (a b : Affine) (hab : le a b) (hba : le b a) : a = b := by
  cases a <;> cases b <;> simp_all only [le, rank] <;> first | rfl | omega

theorem add_le_add_left' (a b : Affine) (h : le a b) (c : Affine) :
    le (add c a) (add c b) := by
  cases a <;> cases b <;> cases c <;> simp only [le, add, rank] at h ⊢ <;> omega

theorem mul_le_mul_left' (a b : Affine) (h : le a b) (c : Affine) :
    le (mul c a) (mul c b) := by
  cases a <;> cases b <;> cases c <;> simp only [le, mul, rank] at h ⊢ <;> omega

theorem mul_le_mul_right' (a b : Affine) (h : le a b) (c : Affine) :
    le (mul a c) (mul b c) := by
  cases a <;> cases b <;> cases c <;> simp only [le, mul, rank] at h ⊢ <;> omega

instance instResourceAlgebra : Resource.ResourceAlgebra Affine where
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

instance : Resource.PartialOrderedResourceAlgebra Affine where
  le_antisymm := le_antisymm'

-- Smoke tests.
example : Resource.ResourceAlgebra Affine := inferInstance
example : le .zero .one := by simp [le, rank]      -- weakening: 0 ⊑ 1 (unlike Linear)
example : le .one .omega := by simp [le, rank]
example : add .one .one = .omega := rfl

end Affine
end Resource.Instances
