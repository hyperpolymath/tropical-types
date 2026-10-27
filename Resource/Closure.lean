-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
import Resource.Algebra.ParametricLaws
import Resource.Instances.MinPlus
import Resource.Instances.MinMax

/-!
  # Resource Algebra — the Kleene / Floyd–Warshall all-pairs closure layer

  Author: Jonathan D.A. Jewell (hyperpolymath)
  Verified: Lean 4.35.0 (pinned via `lean-toolchain`), `import Init` only (no
  Mathlib; we import the Mathlib-free `Resource.*` axis).

  ## What this module is

  An `n × n` **matrix layer over an arbitrary `[ResourceAlgebra R]`**, with
  matrix add (pointwise `⊞`), matrix mul (the `⊞`/`⊠` semiring product), the
  zero and identity matrices, matrix power, and the **Kleene star / closure**

      A* = I ⊞ A ⊞ A² ⊞ … ⊞ A^(n-1).

  Because the whole construction is parametric over the `ResourceAlgebra`
  interface, it instantiates *for free* at:

  * `Resource.Instances.MinPlus` — `⊞ = min`, `⊠ = +`, so `A*` is the
    **all-pairs shortest-path / least-cost** matrix (classical Floyd–Warshall);
  * `Resource.Instances.MinMax`  — `⊞ = min`, `⊠ = max`, so `A*` is the
    **all-pairs bottleneck closure** (the widest / least-bottleneck route, the
    matrix-level form of `Bridge.hub_ceiling`).

  This is the one genuinely-new contribution `typed-wasm` held that the Lean
  `Resource.*` axis lacked: the closure math previously lived only in the
  unbridged Isabelle `.thy` files and in `typed-wasm`'s Idris `Tropical.idr`
  (`CostMatrix`, `costMatStar`, `EntryBounded`, `AllPairsCosts`).  This module
  brings it onto the canonical Lean axis and proves it *once* against the
  interface, so both tropical instances inherit it.

  ## What is proved here (load-bearing, all closed by the prover)

  * `matAdd` is **associative** and **commutative**, with the zero matrix as
    two-sided identity — directly from the semiring laws, pointwise.
  * `lsum_mono` (generalised-sum monotonicity) ⇒ **`matMul`, `matPow` and
    `matStar` are all `⊑`-monotone**: refining the input matrix entrywise refines
    every entry of the product, the powers, and the closure.  This is the
    abstract counterpart of `typed-wasm`'s `EntryBounded` / `AllPairsCosts`
    bound certificate.
  * `EntryBounded` / `AllPairsCosts` mirrors of the Idris records, with the
    closure-entry bound proved from per-power bounds (entrywise `⊑`).
  * `id_le_star` (under an `absorb` hypothesis that every **dioid** supplies):
    `I ⊑ A*` entrywise — the closure subsumes the identity (every node reaches
    itself at zero cost / zero bottleneck).  Witnessed at both `MinPlus` and
    `MinMax` in §8.

  ## Design note on `absorb`

  The bare `ResourceAlgebra` interface does **not** make `a ⊑ a ⊞ b` hold — that
  is an *idempotent-add* (dioid) fact, not a general semiring one (the `{0,1,ω}`
  usage instances are non-idempotent, so it genuinely fails there).  Rather than
  silently assume it, the §6 lemmas that need it take it as an explicit
  hypothesis `absorb : ∀ a b, a ⊑ a ⊞ b`, and §8 discharges it for the two
  tropical dioid instances.  This keeps the abstract layer honest while still
  giving both instances the all-pairs identity-subsumption fact.

  Proof-debt-clean: no incomplete-proof tactics, no compiled-decision escape
  hatch, and no axiom declarations (per the trusted-base reduction policy).
-/

namespace Resource.Closure

open scoped Resource.ResourceSemiring Resource.ResourceAlgebra

-- ============================================================================
-- 0.  Enumerating `Fin n`  (Init has no `List.finRange`)
-- ============================================================================

/-- Every index of `Fin n`, as a concrete list.  Core `Init` ships no
    `List.finRange`, so we build it by structural recursion (mirrors the
    `List.allFins` used in `typed-wasm`'s `Tropical.idr`). -/
def allFins : (n : Nat) → List (Fin n)
  | 0     => []
  | (n+1) => ⟨0, Nat.succ_pos n⟩ :: (allFins n).map Fin.succ

/-- `allFins n` is complete: it contains every index of `Fin n`.  This is what
    guarantees the matrix product folds over *all* intermediate nodes. -/
theorem mem_allFins : ∀ (n : Nat) (i : Fin n), i ∈ allFins n := by
  intro n
  induction n with
  | zero => intro i; exact absurd i.isLt (by omega)
  | succ m ih =>
    intro i
    match i with
    | ⟨0, _⟩ => exact List.mem_cons_self
    | ⟨k+1, h⟩ =>
      apply List.mem_cons_of_mem
      have hmem : (⟨k, by omega⟩ : Fin m) ∈ allFins m := ih _
      have := List.mem_map_of_mem (f := Fin.succ) hmem
      simpa [Fin.succ] using this

-- ============================================================================
-- 1.  Generalised sum over a list, and its monotonicity
-- ============================================================================

variable {R : Type u} [Resource.ResourceAlgebra R]

/-- `lsum l = l₀ ⊞ l₁ ⊞ … ⊞ 0` — the iterated resource choice over a list of
    grades (the `⊞`-fold used by the matrix product). -/
def lsum (l : List R) : R :=
  l.foldr Resource.ResourceSemiring.add Resource.ResourceSemiring.zero

@[simp] theorem lsum_nil : lsum ([] : List R) = (Resource.ResourceSemiring.zero : R) := rfl

@[simp] theorem lsum_cons (a : R) (l : List R) :
    lsum (a :: l) = a ⊞ lsum l := rfl

/-- **Generalised-sum monotonicity.**  If `f b ⊑ g b` pointwise over the list,
    then the `⊞`-sum of the `f`-values refines the `⊞`-sum of the `g`-values.
    This is the single abstract fact that makes the whole closure layer
    `⊑`-monotone — proved from `add_le_add` in `ParametricLaws`. -/
theorem lsum_mono {β : Type v} (l : List β) (f g : β → R)
    (h : ∀ b ∈ l, (f b) ⊑ (g b)) : (lsum (l.map f)) ⊑ (lsum (l.map g)) := by
  induction l with
  | nil => exact Resource.ResourceAlgebra.le_refl _
  | cons x xs ih =>
    simp only [List.map_cons, lsum_cons]
    have hx : (f x) ⊑ (g x) := h x (List.mem_cons_self)
    have hrest : (lsum (xs.map f)) ⊑ (lsum (xs.map g)) :=
      ih (fun b hb => h b (List.mem_cons_of_mem _ hb))
    exact Resource.add_le_add hx hrest

-- ============================================================================
-- 2.  The matrix type and its operations
-- ============================================================================

/-- An `n × n` matrix of resource grades: entry `(i,j)` is the direct grade
    (cost / bottleneck) from node `i` to node `j`. -/
def Mat (n : Nat) (R : Type u) : Type u := Fin n → Fin n → R

/-- The zero matrix: every entry is the additive `zero` (`+∞` in the tropical
    instances — "no edge"). -/
def matZero {n : Nat} : Mat n R := fun _ _ => Resource.ResourceSemiring.zero

/-- The identity matrix: `one` on the diagonal (free self-access), `zero` off it. -/
def matId {n : Nat} : Mat n R :=
  fun i j => if i = j then Resource.ResourceSemiring.one else Resource.ResourceSemiring.zero

/-- Matrix addition: pointwise choice `⊞`. -/
def matAdd {n : Nat} (A B : Mat n R) : Mat n R :=
  fun i j => A i j ⊞ B i j

/-- Matrix multiplication in the resource semiring:
    `(A ⊠ B)(i,j) = ⊞_k  A(i,k) ⊠ B(k,j)`  (least-cost / bottleneck over the
    intermediate node `k`). -/
def matMul {n : Nat} (A B : Mat n R) : Mat n R :=
  fun i j => lsum ((allFins n).map (fun k => A i k ⊠ B k j))

/-- The `p`-th matrix power, `A^p` (with `A^0 = I`). -/
def matPow {n : Nat} (A : Mat n R) : Nat → Mat n R
  | 0     => matId
  | (p+1) => matMul A (matPow A p)

/-- Sum of the first `p` powers, `I ⊞ A ⊞ A² ⊞ … ⊞ A^(p-1)` (empty sum `= 0`). -/
def matPowSum {n : Nat} (A : Mat n R) : Nat → Mat n R
  | 0     => matZero
  | (p+1) => matAdd (matPow A p) (matPowSum A p)

/-- **The Kleene star / closure**: `A* = I ⊞ A ⊞ A² ⊞ … ⊞ A^(n-1)`.

    For an `n`-node graph, `n` powers (`0 … n-1`) suffice, because a simple path
    visits each node at most once.  At `Resource.Instances.MinPlus` this is the
    all-pairs shortest-path matrix (Floyd–Warshall); at `Resource.Instances.MinMax`
    it is the all-pairs bottleneck closure. -/
def matStar {n : Nat} (A : Mat n R) : Mat n R := matPowSum A n

-- ============================================================================
-- 3.  Entrywise order on matrices
-- ============================================================================

/-- Entrywise refinement: `A ⊑ₘ B` iff `A i j ⊑ B i j` for all `i, j`. -/
def matLe {n : Nat} (A B : Mat n R) : Prop := ∀ i j, (A i j) ⊑ (B i j)

@[inherit_doc] scoped infix:50 " ⊑ₘ " => matLe

theorem matLe_refl {n : Nat} (A : Mat n R) : A ⊑ₘ A :=
  fun _ _ => Resource.ResourceAlgebra.le_refl _

theorem matLe_trans {n : Nat} {A B C : Mat n R}
    (hAB : A ⊑ₘ B) (hBC : B ⊑ₘ C) : A ⊑ₘ C :=
  fun i j => Resource.ResourceAlgebra.le_trans _ _ _ (hAB i j) (hBC i j)

-- ============================================================================
-- 4.  Matrix-add laws (associativity, commutativity, identity) — pointwise
-- ============================================================================

theorem matAdd_assoc {n : Nat} (A B C : Mat n R) :
    matAdd (matAdd A B) C = matAdd A (matAdd B C) := by
  funext i j; exact Resource.ResourceSemiring.add_assoc _ _ _

theorem matAdd_comm {n : Nat} (A B : Mat n R) :
    matAdd A B = matAdd B A := by
  funext i j; exact Resource.ResourceSemiring.add_comm _ _

theorem matZero_add {n : Nat} (A : Mat n R) : matAdd matZero A = A := by
  funext i j; exact Resource.ResourceSemiring.zero_add _

theorem matAdd_zero {n : Nat} (A : Mat n R) : matAdd A matZero = A := by
  funext i j; exact Resource.ResourceSemiring.add_zero _

-- ============================================================================
-- 5.  Monotonicity of mul / power / sum / closure  (the load-bearing facts)
-- ============================================================================

theorem matAdd_mono {n : Nat} {A B C D : Mat n R}
    (hAB : A ⊑ₘ B) (hCD : C ⊑ₘ D) : matAdd A C ⊑ₘ matAdd B D :=
  fun i j => Resource.add_le_add (hAB i j) (hCD i j)

/-- `matMul` is monotone in **both** arguments (entrywise): refining either
    factor refines every entry of the product.  Proved by `lsum_mono` from the
    interface's two-sided `mul` monotonicity. -/
theorem matMul_mono {n : Nat} {A B C D : Mat n R}
    (hAB : A ⊑ₘ B) (hCD : C ⊑ₘ D) : matMul A C ⊑ₘ matMul B D := by
  intro i j
  refine lsum_mono (allFins n) (fun k => A i k ⊠ C k j) (fun k => B i k ⊠ D k j) ?_
  intro k _
  exact Resource.mul_le_mul (hAB i k) (hCD k j)

/-- `matPow` is monotone: a refinement of the matrix refines every power. -/
theorem matPow_mono {n : Nat} {A B : Mat n R} (hAB : A ⊑ₘ B) :
    ∀ p, matPow A p ⊑ₘ matPow B p
  | 0     => matLe_refl _
  | (p+1) => matMul_mono hAB (matPow_mono hAB p)

/-- The power sum is monotone. -/
theorem matPowSum_mono {n : Nat} {A B : Mat n R} (hAB : A ⊑ₘ B) :
    ∀ p, matPowSum A p ⊑ₘ matPowSum B p
  | 0     => matLe_refl _
  | (p+1) => matAdd_mono (matPow_mono hAB p) (matPowSum_mono hAB p)

/-- **The headline monotonicity fact: closure is `⊑`-monotone.**  If `A`
    refines `B` entrywise, then `A*` refines `B*` entrywise — at `MinPlus`,
    cheaper edges give an all-pairs matrix that is no more costly everywhere;
    at `MinMax`, lower-bottleneck edges give a closure with no worse bottleneck
    anywhere.  This is the abstract form of `typed-wasm`'s `EntryBounded`. -/
theorem matStar_mono {n : Nat} {A B : Mat n R} (hAB : A ⊑ₘ B) :
    matStar A ⊑ₘ matStar B :=
  matPowSum_mono hAB n

-- ============================================================================
-- 6.  The identity is subsumed by the closure  (`I ⊑ A*`, dioid-only)
-- ============================================================================

/-- A *dioid absorption* witness: `a ⊑ a ⊞ b`.  This is **not** a general
    `ResourceAlgebra` law (it fails for the non-idempotent `{0,1,ω}` usage
    instances), so the lemmas below take it explicitly; both tropical instances
    supply it in §8. -/
abbrev Absorb (R : Type u) [Resource.ResourceAlgebra R] : Prop :=
  ∀ a b : R, a ⊑ (a ⊞ b)

/-- Under absorption, each member of a list is `⊑` the list's `⊞`-sum. -/
theorem le_lsum_of_mem (hab : Absorb R) {a : R} :
    ∀ {l : List R}, a ∈ l → a ⊑ lsum l := by
  intro l
  induction l with
  | nil => intro h; exact absurd h List.not_mem_nil
  | cons x xs ih =>
    intro h
    rcases List.mem_cons.mp h with hx | hxs
    · subst hx; simpa using hab a (lsum xs)
    · refine Resource.ResourceAlgebra.le_trans _ _ _ (ih hxs) ?_
      -- lsum xs ⊑ x ⊞ lsum xs   (absorption after commuting)
      have h1 : lsum xs ⊑ (lsum xs ⊞ x) := hab (lsum xs) x
      have h2 : (lsum xs ⊞ x) = (x ⊞ lsum xs) := Resource.ResourceSemiring.add_comm _ _
      simpa [lsum_cons, h2] using h1

/-- Under absorption, the `p+1`-st power sum subsumes each individual term it
    contains; in particular it subsumes `matId` (the `p = 0` slice). -/
theorem matId_le_matPowSum (hab : Absorb R) {n : Nat} (A : Mat n R) :
    ∀ p, matId ⊑ₘ matPowSum A (p + 1)
  | 0 => by
      intro i j
      -- matPowSum A 1 = matAdd (matPow A 0) matZero = matAdd matId matZero
      have : matPowSum A 1 i j = (matId (R := R) i j ⊞ matZero i j) := rfl
      rw [this]
      simpa using hab (matId (R := R) i j) (matZero (R := R) i j)
  | (p+1) => by
      intro i j
      -- matPowSum A (p+2) = matAdd (matPow A (p+1)) (matPowSum A (p+1))
      have hrec : matId ⊑ₘ matPowSum A (p + 1) := matId_le_matPowSum hab A p
      have hstep : (matPowSum A (p+1) i j) ⊑ (matPowSum A (p+2) i j) := by
        have : matPowSum A (p+2) i j
             = (matPow A (p+1) i j ⊞ matPowSum A (p+1) i j) := rfl
        rw [this]
        have h1 : matPowSum A (p+1) i j ⊑ (matPowSum A (p+1) i j ⊞ matPow A (p+1) i j) :=
          hab _ _
        have h2 : (matPowSum A (p+1) i j ⊞ matPow A (p+1) i j)
                = (matPow A (p+1) i j ⊞ matPowSum A (p+1) i j) :=
          Resource.ResourceSemiring.add_comm _ _
        rw [h2] at h1; exact h1
      exact Resource.ResourceAlgebra.le_trans _ _ _ (hrec i j) hstep

/-- **`I ⊑ A*`.**  For a non-empty node set the closure subsumes the identity:
    every diagonal entry of `A*` is no worse than `one` (zero cost / zero
    bottleneck self-reach), and every off-diagonal entry no worse than `zero`.
    Requires the dioid absorption witness; discharged for both tropical
    instances in §8. -/
theorem id_le_star (hab : Absorb R) {n : Nat} (A : Mat (n + 1) R) :
    matId ⊑ₘ matStar A :=
  matId_le_matPowSum hab A n

-- ============================================================================
-- 7.  Entry bounds — the `EntryBounded` / `AllPairsCosts` mirror
-- ============================================================================
--
-- Mirrors `typed-wasm`'s `EntryBounded` and `AllPairsCosts` records
-- (`TypedWasm/ABI/Tropical.idr`).  There a bound is a numeric `LTE`; here, on
-- the abstract axis, "bounded by `bound`" is the order fact `entry ⊑ bound`
-- (in the tropical instances, `val n ⊑ val B ⇔ B ≤ n`, i.e. the grade is no
-- more costly / no worse a bottleneck than `B`).

/-- An entry is *bounded by* `bound : R` exactly when it refines `bound`. -/
def EntryBounded (entry bound : R) : Prop := entry ⊑ bound

/-- An all-pairs cost certificate: the direct-cost matrix, its closure, a uniform
    per-entry bound, and a proof that every closure entry meets the bound.
    Direct mirror of `AllPairsCosts` in `typed-wasm`'s `Tropical.idr`. -/
structure AllPairsCosts (n : Nat) (R : Type u) [Resource.ResourceAlgebra R] where
  /-- The raw `n × n` direct-grade matrix. -/
  directCosts : Mat n R
  /-- The star-closed all-pairs matrix. -/
  starCosts   : Mat n R
  /-- The star is genuinely the closure of the direct matrix. -/
  isClosure   : starCosts = matStar directCosts
  /-- The declared uniform per-entry bound. -/
  bound       : R
  /-- Every closure entry meets the bound. -/
  bounded     : ∀ i j, EntryBounded (starCosts i j) bound

/-- If a refinement `B` of `A` already has all closure entries bounded, then so
    does `A` (closure monotonicity carries the bound down).  This is the
    abstract form of "a cheaper graph keeps the all-pairs bound", and the reason
    the `AllPairsCosts` certificate is stable under edge improvement. -/
theorem allPairs_bound_of_refine {n : Nat} {A B : Mat n R}
    (hAB : A ⊑ₘ B) {bd : R} (hB : ∀ i j, EntryBounded (matStar B i j) bd) :
    ∀ i j, EntryBounded (matStar A i j) bd := by
  intro i j
  exact Resource.ResourceAlgebra.le_trans _ _ _ (matStar_mono hAB i j) (hB i j)

end Resource.Closure

-- ============================================================================
-- 8.  Instance witnesses — MinPlus (shortest path) and MinMax (bottleneck)
-- ============================================================================

namespace Resource.Closure.Witness

open scoped Resource.ResourceSemiring Resource.ResourceAlgebra
open Resource.Closure

-- ── 8a.  MinPlus: all-pairs least cost (Floyd–Warshall) ──────────────────────

section MinPlus
open Resource.Instances.MinPlus

/-- Absorption holds at `MinPlus` (it is a dioid: `min` is idempotent). -/
theorem minplus_absorb : Absorb MinPlus := by
  intro a b
  show MinPlus.add a (MinPlus.add a b) = MinPlus.add a b
  cases a <;> cases b <;> simp [MinPlus.add, Nat.min_assoc, Nat.min_self]

/-- A worked `2 × 2` least-cost graph:
    `0 →¹ 1`, `1 →¹ 0`, no self-edges given directly.
    Entry `(i,j)` is the direct cost; `top` means "no direct edge". -/
def g2 : Mat 2 MinPlus := fun i j =>
  match i, j with
  | ⟨0, _⟩, ⟨1, _⟩ => .val 1     -- 0 → 1 costs 1
  | ⟨1, _⟩, ⟨0, _⟩ => .val 1     -- 1 → 0 costs 1
  | _,      _      => .top       -- no other direct edge

/-- Smoke test: the closure `g2*` reaches `0 → 0` at cost `0` (the identity
    contributes the free self-loop), and `0 → 1` at cost `1`. -/
example : matStar g2 ⟨0, by omega⟩ ⟨0, by omega⟩ = MinPlus.val 0 := by decide
example : matStar g2 ⟨0, by omega⟩ ⟨1, by omega⟩ = MinPlus.val 1 := by decide

/-- The closure is `⊑`-monotone at `MinPlus` (instantiating the abstract fact). -/
example {A B : Mat 3 MinPlus} (h : A ⊑ₘ B) : matStar A ⊑ₘ matStar B :=
  matStar_mono h

/-- `I ⊑ g2*` at `MinPlus` — the all-pairs matrix subsumes free self-access. -/
example : matId ⊑ₘ matStar g2 := id_le_star minplus_absorb g2

end MinPlus

-- ── 8b.  MinMax: all-pairs bottleneck closure ────────────────────────────────

section MinMax
open Resource.Instances.MinMax

/-- Absorption holds at `MinMax` (also a dioid: `min` is idempotent). -/
theorem minmax_absorb : Absorb MinMax := by
  intro a b
  show MinMax.add a (MinMax.add a b) = MinMax.add a b
  cases a <;> cases b <;> simp [MinMax.add, Nat.min_assoc, Nat.min_self]

/-- A worked `2 × 2` bottleneck graph: `0 → 1` over a link of capacity-cost `5`,
    `1 → 0` over a link of capacity-cost `3`. -/
def b2 : Mat 2 MinMax := fun i j =>
  match i, j with
  | ⟨0, _⟩, ⟨1, _⟩ => .val 5
  | ⟨1, _⟩, ⟨0, _⟩ => .val 3
  | _,      _      => .top

/-- Smoke test: the bottleneck closure reaches `0 → 0` at bottleneck `0` (free
    self-loop from the identity) and `0 → 1` at bottleneck `5` (the worst step
    on the direct edge). -/
example : matStar b2 ⟨0, by omega⟩ ⟨0, by omega⟩ = MinMax.val 0 := by decide
example : matStar b2 ⟨0, by omega⟩ ⟨1, by omega⟩ = MinMax.val 5 := by decide

/-- The bottleneck closure is `⊑`-monotone at `MinMax`: lowering an edge's
    bottleneck cannot worsen any all-pairs bottleneck (the matrix-level
    `hub_ceiling` monotonicity). -/
example {A B : Mat 3 MinMax} (h : A ⊑ₘ B) : matStar A ⊑ₘ matStar B :=
  matStar_mono h

/-- `I ⊑ b2*` at `MinMax`. -/
example : matId ⊑ₘ matStar b2 := id_le_star minmax_absorb b2

end MinMax

end Resource.Closure.Witness
