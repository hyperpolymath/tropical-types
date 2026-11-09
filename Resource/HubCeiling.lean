-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
import Resource.Closure
import Resource.EchoBridge

/-!
  # Resource Algebra — hub ceilings, reach grades and weighted residue measures

  Author: Jonathan D.A. Jewell (hyperpolymath)
  Verified: Lean 4.35.0 (pinned via `lean-toolchain`), `import Init` only (no
  Mathlib).

  ## Why this module exists

  `hyperpolymath/squeakwell` (database recovery through cross-modal constraint
  propagation on VeriSimDB) reads a modality's *reachability* through the
  regeneration graph as a tropical grade: a recovered modality is only as good
  as the worst hop that produced it.  Its route plan (section 6, rungs R5–R7)
  asks this axis for three things, each stated against the abstract
  `ResourceAlgebra` interface so every tropical instance inherits it:

  * **R6 — hub ceiling, element form.**  `TropicalAdapterPath.hub_ceiling` is a
    statement about `List TransportClass` paths and does not transfer to the
    matrix closure literally.  The algebraic kernel does: when the
    multiplicative unit is the **top** of the order (`∀ a, a ⊑ one` — true for
    `MinPlus` and `MinMax`, false for `MaxPlus`), every factor bounds the
    product: `a ⊠ b ⊑ a` and `a ⊠ b ⊑ b` (`factor_le`, `factor_le_right`).
    With dioid absorption and idempotence this lifts to joins and to the
    generalised sum (`join_bound`, `lsum_bound`), and then to matrix products
    (`matMul_row_bound`, `single_hub_ceiling`).  The *star* corollary
    (`single_hub_star_ceiling`) is stated only under an explicit `IsStar`
    hypothesis — the Kleene fixed-point equation `S = I ⊞ A ⊠ S` — because the
    repository has no walk semantics for `matStar` in Lean; that larger item is
    not on squeakwell's critical path.
  * **R7 — reach grade.**  `reachGrade A S m` is the `⊞`-sum of the closure
    entries `A* k m` over the OBSERVED set `S` (a `Bool` predicate on nodes):
    "how well can `m` be reached from what was actually observed".  Proved:
    monotone in the matrix (`reachGrade_mono_mat`), monotone in the observed
    set (`reachGrade_mono_set`, via the new `lsum_filter_mono`), and an
    observed modality has the full grade (`one_le_reachGrade`: `one ⊑
    reachGrade A S m` whenever `S m = true`).
  * **R5 — weighted residue measure.**  The generic free-monoid homomorphism
    `weightedResidueMeasure w : ResidueMeasure (List M) R`, sending a residue
    list to the `⊠`-product of its per-event weights.  Only `one_mul` and
    `mul_assoc` are used, so it is a `ResidueMeasure` for EVERY resource
    algebra; `echoResidueAsMaxPlusCost` is recovered as the constant-weight
    instance.  Residues stay opaque: nothing here makes `List M` a resource
    algebra (the `EchoBridge` boundary invariant is preserved).

  ## Hypotheses are explicit

  Nothing here extends the `ResourceAlgebra` interface.  `one_top`, `Absorb`
  and idempotence are taken as hypotheses where needed and discharged for
  `MinPlus` and `MinMax` in §6; `MaxPlus` is shown NOT to satisfy `one_top`,
  which is why the hub ceiling is a bottleneck/least-cost fact and not a
  general one.

  Proof-debt-clean: no incomplete-proof tactics, no axiom declarations.
-/

namespace Resource.HubCeiling

open scoped Resource.ResourceSemiring Resource.ResourceAlgebra
open Resource.Closure

variable {R : Type u} [Resource.ResourceAlgebra R]

-- ============================================================================
-- 1.  Element-level hub ceiling (R6)
-- ============================================================================

/-- The multiplicative unit is the top of the order: every grade refines
    `one`.  Holds in `MinPlus` / `MinMax` (`one = val 0`, the best grade); fails
    in `MaxPlus`. -/
abbrev OneTop (R : Type u) [Resource.ResourceAlgebra R] : Prop :=
  ∀ a : R, a ⊑ (Resource.ResourceSemiring.one : R)

/-- Idempotent choice: `a ⊞ a = a` (the dioid law). -/
abbrev Idem (R : Type u) [Resource.ResourceAlgebra R] : Prop :=
  ∀ a : R, (a ⊞ a) = a

/-- **Hub ceiling, left factor.**  A composed grade is no better than its first
    factor: one bad hop caps the whole route. -/
theorem factor_le (htop : OneTop R) (a b : R) : (a ⊠ b) ⊑ a := by
  have h := Resource.ResourceAlgebra.mul_le_mul_left b (Resource.ResourceSemiring.one : R) (htop b) a
  rw [Resource.ResourceSemiring.mul_one] at h
  exact h

/-- **Hub ceiling, right factor.** -/
theorem factor_le_right (htop : OneTop R) (a b : R) : (a ⊠ b) ⊑ b := by
  have h := Resource.ResourceAlgebra.mul_le_mul_right a (Resource.ResourceSemiring.one : R) (htop a) b
  rw [Resource.ResourceSemiring.one_mul] at h
  exact h

/-- Under absorption `zero` is the bottom of the order ("no route" is the worst
    grade). -/
theorem zero_bot (hab : Absorb R) (a : R) : (Resource.ResourceSemiring.zero : R) ⊑ a := by
  have h := hab (Resource.ResourceSemiring.zero : R) a
  rw [Resource.ResourceSemiring.zero_add] at h
  exact h

/-- A join of two grades below `c` stays below `c` (needs idempotence). -/
theorem join_bound (idem : Idem R) {a b c : R} (ha : a ⊑ c) (hb : b ⊑ c) : (a ⊞ b) ⊑ c := by
  have h := Resource.add_le_add ha hb
  rw [idem c] at h
  exact h

/-- The generalised sum of grades all below `c` is below `c`. -/
theorem lsum_bound (idem : Idem R) (hab : Absorb R) {c : R} :
    ∀ {l : List R}, (∀ x ∈ l, x ⊑ c) → lsum l ⊑ c := by
  intro l
  induction l with
  | nil => intro _; exact zero_bot hab c
  | cons x xs ih =>
    intro h
    rw [lsum_cons]
    exact join_bound idem (h x (List.mem_cons_self)) (ih (fun y hy => h y (List.mem_cons_of_mem _ hy)))

/-- Each product term of a matrix entry is bounded by its left factor, so the
    whole entry is bounded by the `⊞`-sum of the left row. -/
theorem matMul_row_bound (htop : OneTop R) {n : Nat} (A B : Mat n R) (i j : Fin n) :
    matMul A B i j ⊑ lsum ((allFins n).map (fun k => A i k)) := by
  unfold matMul
  refine lsum_mono (allFins n) (fun k => A i k ⊠ B k j) (fun k => A i k) ?_
  intro k _
  exact factor_le htop _ _

/-- A node `i` whose only outgoing edge goes to the hub `h`. -/
def SingleHub {n : Nat} (A : Mat n R) (i h : Fin n) : Prop :=
  ∀ k, k ≠ h → A i k = (Resource.ResourceSemiring.zero : R)

/-- **Single-hub ceiling.**  If every route out of `i` passes through the hub
    `h`, then every composed route from `i` is capped by the hub edge. -/
theorem single_hub_ceiling (htop : OneTop R) (idem : Idem R) (hab : Absorb R)
    {n : Nat} (A B : Mat n R) {i h : Fin n} (hs : SingleHub A i h) (j : Fin n) :
    matMul A B i j ⊑ A i h := by
  unfold matMul
  apply lsum_bound idem hab
  intro x hx
  rcases List.mem_map.mp hx with ⟨k, _, rfl⟩
  by_cases hk : k = h
  · subst hk; exact factor_le htop _ _
  · rw [hs k hk, Resource.ResourceSemiring.zero_mul]
    exact zero_bot hab _

/-- The Kleene fixed-point equation.  `matStar` is one solution in the walk
    semantics this repository does not yet formalise in Lean; the corollary
    below therefore takes the equation as an explicit hypothesis. -/
def IsStar {n : Nat} (A S : Mat n R) : Prop :=
  S = matAdd matId (matMul A S)

/-- **Single-hub ceiling for a closure.**  Under `IsStar`, every off-diagonal
    closure entry out of a single-hub node is capped by the hub edge. -/
theorem single_hub_star_ceiling (htop : OneTop R) (idem : Idem R) (hab : Absorb R)
    {n : Nat} {A S : Mat n R} (hS : IsStar A S) {i h : Fin n} (hs : SingleHub A i h)
    (j : Fin n) (hij : i ≠ j) : S i j ⊑ A i h := by
  have hentry : S i j = (matId i j ⊞ matMul A S i j) :=
    congrFun (congrFun hS i) j
  rw [hentry]
  have hid : matId (R := R) i j = (Resource.ResourceSemiring.zero : R) := by
    unfold matId; simp [hij]
  rw [hid, Resource.ResourceSemiring.zero_add]
  exact single_hub_ceiling htop idem hab A S hs j

-- ============================================================================
-- 2.  Sums over filtered lists (the lemma R7 needs)
-- ============================================================================

/-- Enlarging the observed set can only improve the sum: under absorption,
    `lsum` over the `S`-filtered list refines `lsum` over the `T`-filtered list
    whenever `S ⊆ T`. -/
theorem lsum_filter_mono (hab : Absorb R) {β : Type v} (l : List β) (S T : β → Bool)
    (f : β → R) (hST : ∀ b, S b = true → T b = true) :
    lsum ((l.filter S).map f) ⊑ lsum ((l.filter T).map f) := by
  induction l with
  | nil => exact Resource.ResourceAlgebra.le_refl _
  | cons x xs ih =>
    by_cases hs : S x = true
    · have ht : T x = true := hST x hs
      rw [List.filter_cons_of_pos hs, List.filter_cons_of_pos ht]
      simp only [List.map_cons, lsum_cons]
      exact Resource.ResourceAlgebra.add_le_add_left _ _ ih _
    · have hs' : ¬ (S x = true) := hs
      rw [List.filter_cons_of_neg hs']
      by_cases ht : T x = true
      · rw [List.filter_cons_of_pos ht]
        simp only [List.map_cons, lsum_cons]
        refine Resource.ResourceAlgebra.le_trans _ _ _ ih ?_
        have h1 := hab (lsum ((xs.filter T).map f)) (f x)
        rw [Resource.ResourceSemiring.add_comm] at h1
        exact h1
      · rw [List.filter_cons_of_neg ht]
        exact ih

-- ============================================================================
-- 3.  Reach grades (R7)
-- ============================================================================

/-- The reach grade of node `m` from the observed set `S`: the `⊞`-sum (best
    choice) of the closure entries `A* k m` over the observed nodes `k`. -/
def reachGrade {n : Nat} (A : Mat n R) (S : Fin n → Bool) (m : Fin n) : R :=
  lsum (((allFins n).filter S).map (fun k => matStar A k m))

/-- Refining the regeneration matrix refines every reach grade. -/
theorem reachGrade_mono_mat {n : Nat} {A B : Mat n R} (hAB : A ⊑ₘ B)
    (S : Fin n → Bool) (m : Fin n) : reachGrade A S m ⊑ reachGrade B S m := by
  unfold reachGrade
  refine lsum_mono _ (fun k => matStar A k m) (fun k => matStar B k m) ?_
  intro k _
  exact matStar_mono hAB k m

/-- Observing more never lowers a reach grade. -/
theorem reachGrade_mono_set (hab : Absorb R) {n : Nat} (A : Mat n R)
    {S T : Fin n → Bool} (hST : ∀ k, S k = true → T k = true) (m : Fin n) :
    reachGrade A S m ⊑ reachGrade A T m :=
  lsum_filter_mono hab (allFins n) S T (fun k => matStar A k m) hST

/-- An observed node has the full grade: `one ⊑ reachGrade A S m` when
    `S m = true` (the closure's free self-loop is among the summands). -/
theorem one_le_reachGrade (hab : Absorb R) {n : Nat} (A : Mat (n + 1) R)
    (S : Fin (n + 1) → Bool) (m : Fin (n + 1)) (hm : S m = true) :
    (Resource.ResourceSemiring.one : R) ⊑ reachGrade A S m := by
  unfold reachGrade
  have hdiag : (Resource.ResourceSemiring.one : R) ⊑ matStar A m m := by
    have h := id_le_star hab A m m
    unfold matId at h
    simpa using h
  refine Resource.ResourceAlgebra.le_trans _ _ _ hdiag ?_
  apply le_lsum_of_mem hab
  apply List.mem_map.mpr
  refine ⟨m, ?_, rfl⟩
  exact List.mem_filter.mpr ⟨mem_allFins _ m, hm⟩

-- ============================================================================
-- 4.  Weighted residue measures (R5)
-- ============================================================================

end Resource.HubCeiling

namespace Resource.HubCeiling

open scoped Resource.ResourceSemiring Resource.ResourceAlgebra

-- `ResidueMeasure` lives at `Type` (its carriers are `Type`, not `Type u`), so
-- this section is at universe zero.
variable {R : Type} [Resource.ResourceAlgebra R]

/-- The `⊠`-product of per-event weights over a residue list. -/
def weightedMeasure {M : Type} (w : M → R) : List M → R
  | []      => Resource.ResourceSemiring.one
  | (m :: l) => w m ⊠ weightedMeasure w l

theorem weightedMeasure_append {M : Type} (w : M → R) (l₁ l₂ : List M) :
    weightedMeasure w (l₁ ++ l₂) = weightedMeasure w l₁ ⊠ weightedMeasure w l₂ := by
  induction l₁ with
  | nil =>
    simp only [List.nil_append, weightedMeasure]
    rw [Resource.ResourceSemiring.one_mul]
  | cons x xs ih =>
    simp only [List.cons_append, weightedMeasure]
    rw [ih, Resource.ResourceSemiring.mul_assoc]

/-- **The generic weighted residue measure.**  For ANY resource algebra `R` and
    ANY weight `w : M → R`, the free monoid of residue events measures into `R`
    as a monoid homomorphism (`one_mul` and `mul_assoc` are all that is used).
    `List M` stays an opaque residue carrier; it is never a resource algebra. -/
def weightedResidueMeasure {M : Type} (w : M → R) : Resource.ResidueMeasure (List M) R where
  combine := List.append
  empty   := []
  measure := weightedMeasure w
  measure_empty   := rfl
  measure_combine := weightedMeasure_append w

end Resource.HubCeiling

-- ============================================================================
-- 5.  The constant-weight instance recovers the existing bridge
-- ============================================================================

namespace Resource.HubCeiling.Witness

open scoped Resource.ResourceSemiring Resource.ResourceAlgebra
open Resource.Closure Resource.HubCeiling

/-- Counting residue events into max-plus is the weighted measure with the
    constant weight `val 1` (`one_mul`-free: both sides compute to the length). -/
theorem weighted_counts_events (l : List Unit) :
    weightedMeasure (fun (_ : Unit) => Hyperpolymath.Tropical.Tropical.val 1) l
      = Hyperpolymath.Tropical.Tropical.val l.length := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [weightedMeasure, List.length_cons, ih]
    show Hyperpolymath.Tropical.tMul _ _ = _
    simp [Hyperpolymath.Tropical.tMul, Nat.add_comm]

-- ============================================================================
-- 6.  Instance witnesses — MinPlus and MinMax satisfy the hypotheses; MaxPlus
--     does not satisfy `OneTop`
-- ============================================================================

section MinMax
open Resource.Instances.MinMax

/-- `one = val 0` is the top of the bottleneck order. -/
theorem minmax_one_top : OneTop MinMax := by
  intro a
  cases a with
  | top => exact MinMax.top_le _
  | val m => exact (MinMax.le_val_val m 0).mpr (Nat.zero_le m)

theorem minmax_idem : Idem MinMax := by
  intro a
  show MinMax.add a a = a
  exact MinMax.add_idem a

/-- The single-hub ceiling instantiated at the bottleneck algebra: a
    regeneration step through one hub is no better than the hub edge. -/
example {A B : Mat 3 MinMax} {i h : Fin 3} (hs : SingleHub A i h) (j : Fin 3) :
    matMul A B i j ⊑ A i h :=
  single_hub_ceiling minmax_one_top minmax_idem
    Resource.Closure.Witness.minmax_absorb A B hs j

/-- Reach grades are monotone in the observed set at `MinMax`. -/
example {A : Mat 3 MinMax} {S T : Fin 3 → Bool} (h : ∀ k, S k = true → T k = true) (m : Fin 3) :
    reachGrade A S m ⊑ reachGrade A T m :=
  reachGrade_mono_set Resource.Closure.Witness.minmax_absorb A h m

/-- An observed modality has the full grade at `MinMax`. -/
example {A : Mat 3 MinMax} (m : Fin 3) :
    (Resource.ResourceSemiring.one : MinMax) ⊑ reachGrade A (fun _ => true) m :=
  one_le_reachGrade Resource.Closure.Witness.minmax_absorb A (fun _ => true) m rfl

end MinMax

section MinPlus
open Resource.Instances.MinPlus

/-- `one = val 0` is the top of the least-cost order. -/
theorem minplus_one_top : OneTop MinPlus := by
  intro a
  cases a with
  | top => exact MinPlus.top_le _
  | val m => exact (MinPlus.le_val_val m 0).mpr (Nat.zero_le m)

theorem minplus_idem : Idem MinPlus := by
  intro a
  show MinPlus.add a a = a
  exact MinPlus.add_idem a

example {A B : Mat 3 MinPlus} {i h : Fin 3} (hs : SingleHub A i h) (j : Fin 3) :
    matMul A B i j ⊑ A i h :=
  single_hub_ceiling minplus_one_top minplus_idem
    Resource.Closure.Witness.minplus_absorb A B hs j

end MinPlus

section MaxPlus
open Resource.Instances.MaxPlus

/-- `MaxPlus` is NOT `OneTop`: `val 1` is strictly better than `one = val 0` in
    the max-plus order, so the hub ceiling does not hold there.  This is the
    honest boundary of R6. -/
theorem maxplus_not_one_top : ¬ OneTop Hyperpolymath.Tropical.Tropical := by
  intro h
  have h1 := h (Hyperpolymath.Tropical.Tropical.val 1)
  have h2 := (le_val_val 1 0).mp h1
  omega

end MaxPlus

end Resource.HubCeiling.Witness
