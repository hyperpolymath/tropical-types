-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
import Resource.Algebra.Interface
import Resource.Algebra.Ordered
import Resource.Algebra.Dioid
import Resource.Algebra.ParametricLaws
import Resource.Instances.Linear
import Resource.Instances.Affine
import Resource.Instances.MaxPlus
import Resource.Instances.MinPlus
import Resource.Instances.MinMax
import Resource.Stress
import Resource.EchoBridge
import Resource.Conformance
import Resource.Bridge
import Resource.Closure

/-!
  # `Resource` — the resource-grade axis (aggregator)

  Author: Jonathan D.A. Jewell (hyperpolymath)
  Verified: Lean 4.35.0 (pinned via `lean-toolchain`), no Mathlib.

  This is the single import a downstream language (e.g. `my-lang`) needs to pick
  up the entire **resource-grade axis** that `tropical-resource-typing` exports.
  See `FOUNDATION_CONTRACT.md` for the boundary invariant and the consumer rule.

  ## Layers

  * `Resource.Algebra.Interface`     — `ResourceSemiring` (the algebra core).
  * `Resource.Algebra.Ordered`       — `ResourceAlgebra` (ordered + monotone),
                                        plus the `PartialOrdered…` refinement.
  * `Resource.Algebra.Dioid`         — canonical-order builder for idempotent
                                        (tropical) semirings; no carrier case-split.
  * `Resource.Algebra.ParametricLaws`— `ConsumerLawBundle` and the transport
                                        theorem `parametric_resource_transport`
                                        (alias `resource_laws_sufficient_for_consumers`).

  ## Instances (all satisfy the one `ResourceAlgebra` interface)

  | module                      | carrier            | `⊞` (choice) | `⊠` (seq) | finite? |
  | --------------------------- | ------------------ | ------------ | --------- | ------- |
  | `Resource.Instances.Linear` | `{0,1,ω}`          | usage-add    | scale     | yes     |
  | `Resource.Instances.Affine` | `{0,1,ω}`          | usage-add    | scale     | yes     |
  | `Resource.Instances.MaxPlus`| `ℕ ∪ {−∞}`         | `max`        | `+`       | NO      |
  | `Resource.Instances.MinPlus`| `ℕ ∪ {+∞}`         | `min`        | `+`       | NO      |
  | `Resource.Instances.MinMax` | `ℕ ∪ {+∞}`         | `min`        | `max`     | NO      |

  * `Resource.Stress`     — the tropical carriers are proved **infinite**.
  * `Resource.EchoBridge` — a resource algebra may *measure* opaque (Echo)
                            residues; Echo is **not** a resource instance.
  * `Resource.Conformance`— all five instances satisfy the one interface, and a
                            parametric consumer lemma instantiates at each.
  * `Resource.Bridge`     — the two original twins (`TropicalSessionTypes`,
                            `TropicalAdapterPath`) exhibited as instances of this
                            axis (QTT refinement and `hub_ceiling` restated in `⊑`).
  * `Resource.Closure`    — the Kleene / Floyd–Warshall all-pairs **closure**
                            layer (`Mat`, `matMul`, `matStar`), parametric over
                            `ResourceAlgebra`; instantiates at `MinPlus`
                            (all-pairs shortest path) and `MinMax` (all-pairs
                            bottleneck).  The `EntryBounded` / `AllPairsCosts`
                            certificate and `matStar` monotonicity mirror
                            `typed-wasm`'s Idris `Tropical.idr` onto the axis.
-/
