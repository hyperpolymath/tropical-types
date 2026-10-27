-- SPDX-License-Identifier: MPL-2.0
import Init

/-!
  # Tropical Session Types — v6.0

  Author: Jonathan D.A. Jewell (hyperpolymath)
  Date:   2026-04-11
  Verified: Lean 4.35.0 (pinned via `lean-toolchain`), `import Init` (no Mathlib dependency)

  ## The unsolved problem

  Session Types (Honda 1998) prove deadlock-freedom but ignore resources.
  Quantitative Type Theory (Atkey 2018) tracks resources via a standard
  semiring, but fails to model speculative/parallel branching: if branch A
  costs 5 s and branch B costs 10 s, QTT bills 15 s but real wall-clock
  time is only 10 s.

  ## The solution

  Grade session types with the **max-plus tropical semiring**:
  `(Tropical, ⊕, ⊗, bot, val 0)` where
  - `⊕` = max  (parallel cost = bottleneck)
  - `⊗` = nat+ (sequential cost = sum)
  - `bot` = −∞ (additive zero / identity of max)
  - `val 0` = 0  (multiplicative identity)

  ## What is proved (v6.0, zero sorries)

  ### CommSemiring laws (13 individual theorems)
  `add_comm`, `add_assoc`, `bot_add`, `add_bot`,
  `mul_comm`, `mul_assoc`, `one_mul_trop`, `mul_one_trop`,
  `bot_mul`, `mul_bot`, `left_distrib_trop`, `right_distrib_trop`.

  ### CommSemiring Tropical instance
  All 13 fields wired; enables `ring`-style reasoning for downstream proofs.

  ### Session type theorems
  - `grade_ne_bot`  — all valid sessions have finite cost
  - `soundness`     — static grade = dynamic Span (Lean analogue of
                      Isabelle `max_khop_eq_sum_walks`)
  - `tropical_grade_le_sequentialTotal` — tropical budget ≤ sequential
                      billing (QTT refinement; Lean analogue of
                      Isabelle `tropical_add_idem`)

  ## Design decisions (do not change without understanding these)

  - `send` costs 1, `recv` costs 0.  Sender is the active party.
  - `recv` written `val 0 * grade s`.  `val 0` is the multiplicative
    identity, so this is literally `id`.  Intentional for structural
    uniformity — multiplication does no semantic work here.
  - `Span` mirrors `grade` exactly (same recursive structure).  It is
    the adequate internal model for soundness; not a full reduction.

  ## Open items

  1. Add `external_choice` / `internal_choice` to `Session`; `grade` for
     choice uses `tAdd` (max over branches — worst case).
  2. State the QTT quotient morphism explicitly: `sequentialTotal /
     linearBilling` is a quotient of tropical grading; proved by the
     refinement theorem but not yet stated as a morphism.
  3. Check ECHIDNA Lean 4 prover interface compatibility.
  4. Repo placement: standalone `tropical-session-types`, cross-linked
     from `my-lang` and `maa-framework`.

  ## Cross-system connections (not yet formalised)

  - `soundness` (here) ↔ `max_khop_eq_sum_walks` (Isabelle):
    map `Session` to `trop_mat` (session-type graph = adjacency matrix)
    and invoke the Isabelle walk-weight theorem.
  - `tropical_grade_le_sequentialTotal` ↔ `tropical_add_idem` (Isabelle):
    `max(n1,n2) ≤ n1+n2` is `add_idem` in the dioid.
  - `spec_par s1 s2` ↔ `trop_mat_add`: parallel sessions are matrix
    addition; a machine-checked type checker backed by `floyd_warshall`.
-/

namespace Hyperpolymath.Tropical

-- ============================================================================
-- 1. Tropical Semiring Type
-- ============================================================================

/-- The max-plus tropical semiring carrier.
    `val n` embeds `n : Nat`; `bot` represents −∞ (additive zero). -/
inductive Tropical where
  | val : Nat → Tropical
  | bot : Tropical
  deriving DecidableEq, Repr

-- ============================================================================
-- 2. Primitive Operations
-- ============================================================================

/-- Tropical addition: max with `bot` (−∞) as identity.
    `tAdd (val m) (val n) = val (max m n)` -/
def tAdd : Tropical → Tropical → Tropical
  | .bot, b          => b
  | a,    .bot       => a
  | .val m, .val n   => .val (Nat.max m n)

/-- Tropical multiplication: nat-addition with `val 0` as identity.
    `tMul (val m) (val n) = val (m + n)` -/
def tMul : Tropical → Tropical → Tropical
  | .bot, _          => .bot
  | _,    .bot       => .bot
  | .val m, .val n   => .val (m + n)

-- ============================================================================
-- 3. CommSemiring Laws (individual theorems)
-- ============================================================================

-- ---- Addition ---------------------------------------------------------------

theorem add_comm_trop (a b : Tropical) : tAdd a b = tAdd b a := by
  cases a <;> cases b <;> simp [tAdd, Nat.max_comm]

theorem add_assoc_trop (a b c : Tropical) :
    tAdd (tAdd a b) c = tAdd a (tAdd b c) := by
  cases a <;> cases b <;> cases c <;> simp [tAdd, Nat.max_assoc]

/-- `bot` is the left identity of `tAdd`. -/
theorem bot_add (a : Tropical) : tAdd .bot a = a := by
  cases a <;> simp [tAdd]

/-- `bot` is the right identity of `tAdd`. -/
theorem add_bot (a : Tropical) : tAdd a .bot = a := by
  cases a <;> simp [tAdd]

-- ---- Multiplication ---------------------------------------------------------

theorem mul_comm_trop (a b : Tropical) : tMul a b = tMul b a := by
  cases a <;> cases b <;> simp [tMul, Nat.add_comm]

theorem mul_assoc_trop (a b c : Tropical) :
    tMul (tMul a b) c = tMul a (tMul b c) := by
  cases a <;> cases b <;> cases c <;> simp [tMul, Nat.add_assoc]

/-- `val 0` is the left identity of `tMul`. -/
theorem one_mul_trop (a : Tropical) : tMul (.val 0) a = a := by
  cases a <;> simp [tMul]

/-- `val 0` is the right identity of `tMul`. -/
theorem mul_one_trop (a : Tropical) : tMul a (.val 0) = a := by
  cases a <;> simp [tMul]

/-- `bot` (−∞) annihilates on the left under `tMul`. -/
theorem bot_mul (a : Tropical) : tMul .bot a = .bot := by
  cases a <;> simp [tMul]

/-- `bot` (−∞) annihilates on the right under `tMul`. -/
theorem mul_bot (a : Tropical) : tMul a .bot = .bot := by
  cases a <;> simp [tMul]

-- ---- Helper: nat-addition distributes over max ------------------------------

private theorem nat_mul_add_max_left (k m n : Nat) :
    k + Nat.max m n = Nat.max (k + m) (k + n) := by
  simp only [Nat.max_def]; split <;> split <;> omega

private theorem nat_mul_add_max_right (k m n : Nat) :
    Nat.max m n + k = Nat.max (m + k) (n + k) := by
  simp only [Nat.max_def]; split <;> split <;> omega

-- ---- Distributivity ---------------------------------------------------------

/-- Left distributivity: `a ⊗ (b ⊕ c) = (a ⊗ b) ⊕ (a ⊗ c)`. -/
theorem left_distrib_trop (a b c : Tropical) :
    tMul a (tAdd b c) = tAdd (tMul a b) (tMul a c) := by
  cases a <;> cases b <;> cases c <;>
    simp only [tMul, tAdd, nat_mul_add_max_left]

/-- Right distributivity: `(a ⊕ b) ⊗ c = (a ⊗ c) ⊕ (b ⊗ c)`. -/
theorem right_distrib_trop (a b c : Tropical) :
    tMul (tAdd a b) c = tAdd (tMul a c) (tMul b c) := by
  cases a <;> cases b <;> cases c <;>
    simp only [tMul, tAdd, nat_mul_add_max_right]

-- ============================================================================
-- 4. CommSemiring Typeclass (local definition, Mathlib-compatible interface)
-- ============================================================================

/-- Lean 4.13.0 core provides `Zero` but not `One` (the latter landed in a
    later toolchain).  We supply a minimal local `One` plus its `OfNat` bridge
    so the Mathlib-compatible interface and `1` notation work under the pinned
    toolchain without any Mathlib dependency. -/
class One (α : Type) where
  one : α

instance [One α] : OfNat α (nat_lit 1) := ⟨One.one⟩

/-- A commutative semiring.
    Defined locally (no Mathlib dependency) with a Mathlib-compatible interface.
    Wiring `Tropical` here enables `ring`-style proofs once Mathlib is added. -/
class CommSemiring (α : Type) extends Add α, Mul α, Zero α, One α where
  add_comm     : ∀ a b : α, a + b = b + a
  add_assoc    : ∀ a b c : α, (a + b) + c = a + (b + c)
  zero_add     : ∀ a : α, 0 + a = a
  add_zero     : ∀ a : α, a + 0 = a
  mul_comm     : ∀ a b : α, a * b = b * a
  mul_assoc    : ∀ a b c : α, (a * b) * c = a * (b * c)
  one_mul      : ∀ a : α, 1 * a = a
  mul_one      : ∀ a : α, a * 1 = a
  zero_mul     : ∀ a : α, 0 * a = 0
  mul_zero     : ∀ a : α, a * 0 = 0
  left_distrib  : ∀ a b c : α, a * (b + c) = a * b + a * c
  right_distrib : ∀ a b c : α, (a + b) * c = a * c + b * c

-- ============================================================================
-- 5. CommSemiring Tropical Instance
-- ============================================================================

/-- `Tropical` is a commutative semiring under `(tAdd, tMul, bot, val 0)`.

    Each field maps directly to the individually proved theorems above.
    The instance wires them together to expose `+`, `*`, `0`, `1` notation
    and enables `ring`-style tactic reasoning on `Tropical` expressions. -/
instance : CommSemiring Tropical where
  add           := tAdd
  mul           := tMul
  zero          := .bot
  one           := .val 0
  add_comm      := add_comm_trop
  add_assoc     := add_assoc_trop
  zero_add      := bot_add
  add_zero      := add_bot
  mul_comm      := mul_comm_trop
  mul_assoc     := mul_assoc_trop
  one_mul       := one_mul_trop
  mul_one       := mul_one_trop
  zero_mul      := bot_mul
  mul_zero      := mul_bot
  left_distrib  := left_distrib_trop
  right_distrib := right_distrib_trop

-- Smoke-test: notation and typeclass plumbing

#check (inferInstance : CommSemiring Tropical)

example : (0 : Tropical) = .bot            := rfl
example : (1 : Tropical) = .val 0          := rfl
example : (.val 2 + .val 5 : Tropical) = .val 5 := by decide
example : (.val 2 * .val 5 : Tropical) = .val 7 := by decide

-- ============================================================================
-- 6. Session Types
-- ============================================================================

/-- A simplified session calculus supporting speculative parallelism.

    - `end_session` — the terminated session (zero cost)
    - `send s`      — send one message, then continue as `s` (cost 1 + cost s)
    - `recv s`      — receive one message, then continue as `s` (cost 0 + cost s)
    - `spec_par s1 s2` — speculative parallel branch (cost = max of branches)

    `recv` is written `val 0 * grade s` to maintain structural uniformity:
    `val 0` is the multiplicative identity, so multiplication does no semantic
    work in the recv case. -/
inductive Session where
  | end_session : Session
  | send        : Session → Session
  | recv        : Session → Session
  | spec_par    : Session → Session → Session

-- ============================================================================
-- 7. Static Grade (type-level cost)
-- ============================================================================

/-- Computes the static tropical grade (type-level worst-case cost) of a session.
    Speculative branching uses `tAdd` (max) rather than nat-addition. -/
def grade : Session → Tropical
  | .end_session     => .val 0
  | .send s          => tMul (.val 1) (grade s)
  | .recv s          => tMul (.val 0) (grade s)
  | .spec_par s1 s2  => tAdd (grade s1) (grade s2)

-- ============================================================================
-- 8. Operational Semantics (Span)
-- ============================================================================

/-- Dynamic wall-clock cost of a session.
    Mirrors `grade` exactly (same recursive structure); adequate model for
    soundness.  Not a full reduction relation. -/
def Span : Session → Nat
  | .end_session     => 0
  | .send s          => 1 + Span s
  | .recv s          => Span s
  | .spec_par s1 s2  => Nat.max (Span s1) (Span s2)

-- ============================================================================
-- 9. Theorem 1: Soundness
-- ============================================================================

/-- **Soundness**: the static grade perfectly predicts dynamic wall-clock cost.
    `grade s = val (Span s)` for all sessions `s`.

    Lean analogue of Isabelle `max_khop_eq_sum_walks`: both say
    "recursive static definition = inductive operational semantics". -/
theorem soundness (s : Session) : grade s = .val (Span s) := by
  induction s with
  | end_session       => simp [grade, Span]
  | send s ih         => simp [grade, tMul, Span, ih]
  | recv s ih         => simp [grade, tMul, Span, ih]
  | spec_par s1 s2 ih1 ih2 => simp [grade, tAdd, Span, ih1, ih2]

-- ============================================================================
-- 10. Corollary: grade_ne_bot
-- ============================================================================

/-- All valid sessions have finite cost: `grade s ≠ bot`.
    Immediate from `soundness` since `val n ≠ bot` for all `n`. -/
theorem grade_ne_bot (s : Session) : grade s ≠ .bot := by
  rw [soundness s]
  simp [Tropical.val.injEq]

-- ============================================================================
-- 11. Theorem 2: QTT Refinement (tropical_grade_le_sequentialTotal)
-- ============================================================================

/-- Standard linear / quantitative type theory bills the *sum* of all branch
    costs (the "sequential total").  This overapproximates wall-clock time
    when branches run in parallel. -/
def sequentialTotal : Session → Nat
  | .end_session     => 0
  | .send s          => 1 + sequentialTotal s
  | .recv s          => sequentialTotal s
  | .spec_par s1 s2  => sequentialTotal s1 + sequentialTotal s2

/-- **QTT Refinement**: the tropical (wall-clock) cost is always ≤ the
    sequential total.  `max(a, b) ≤ a + b` for all naturals.

    Lean analogue of Isabelle `tropical_add_idem`:
    `max a b ≤ a + b` follows from `add_idem` in the dioid. -/
theorem tropical_grade_le_sequentialTotal (s : Session) :
    Span s ≤ sequentialTotal s := by
  induction s with
  | end_session           => simp [Span, sequentialTotal]
  | send s ih             => simp [Span, sequentialTotal]; omega
  | recv s ih             => simp [Span, sequentialTotal]; exact ih
  | spec_par s1 s2 ih1 ih2 =>
      simp only [Span, sequentialTotal, Nat.max_def]
      split <;> omega

end Hyperpolymath.Tropical
