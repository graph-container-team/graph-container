/-
Copyright (c) 2026 Graph Container formalization team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Graph Container formalization team
-/
module

public import GraphContainer.Basic
public import GraphContainer.Intersecting.Basic
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Local density data for Theorem 2.3

This file packages the Kneser-graph calculation needed by the graph container theorem. It does not
expose the separate spectral results appearing later in the PDF. Their combined contribution is the
single local-density interface `isLocallyDense` below.
-/

@[expose] public section

open Finset

namespace SimpleGraph.Kneser

/-- The number of vertices of `graph n k`, written separately for readable estimates. -/
def vertexCount (n k : ℕ) : ℕ := n.choose k

/-- The cardinality of a full star. -/
def starSize (n k : ℕ) : ℕ := (n - 1).choose (k - 1)

/-- The degree of a vertex in the Kneser graph. -/
def regularDegree (n k : ℕ) : ℕ := (n - k).choose k

/-- The local-density constant obtained from the Kneser calculation in the PDF. -/
noncomputable def densityParameter (ε : ℝ) (n k : ℕ) : ℝ :=
  (ε / (1 + ε)) *
    ((regularDegree n k : ℝ) * (n : ℝ) /
      ((vertexCount n k : ℝ) * (n - k : ℝ)))

/-- The integral container threshold corresponding to `(1 + ε) * starSize n k`. -/
noncomputable def containerThreshold (ε : ℝ) (n k : ℕ) : ℕ :=
  ⌈(1 + ε) * (starSize n k : ℝ)⌉₊

/-- The integral fingerprint size used in the container theorem.

The ceiling repairs the paper's use of a real expression for the natural-number parameter `q`.
-/
noncomputable def fingerprintSize (ε : ℝ) (n k : ℕ) : ℕ :=
  ⌈(densityParameter ε n k)⁻¹ *
      Real.log ((vertexCount n k : ℝ) / (containerThreshold ε n k : ℝ))⌉₊

/-- The Kneser graph has the expected regular degree for positive uniformity. -/
theorem isRegularOfDegree (n : ℕ) {k : ℕ} (hk : 0 < k) :
    (graph n k).IsRegularOfDegree (regularDegree n k) := by
  sorry

/-- The combined Kneser calculation supplies the local-density hypothesis used for Theorem 2.3. -/
theorem isLocallyDense
    {ε : ℝ} {n k : ℕ}
    (hε : 0 < ε) (hk : 0 < k) (hnk : 2 * k + 1 ≤ n) :
    Container.IsLocallyDense (graph n k)
      (densityParameter ε n k) (containerThreshold ε n k) := by
  sorry

/-- Positivity of the density parameter in the admissible range. -/
theorem densityParameter_pos
    {ε : ℝ} {n k : ℕ}
    (hε : 0 < ε) (hk : 0 < k) (hnk : 2 * k + 1 ≤ n) :
    0 < densityParameter ε n k := by
  sorry

/-- The density parameter lies below one in the range used by the container theorem. -/
theorem densityParameter_lt_one
    {ε : ℝ} {n k : ℕ}
    (hε : 0 < ε) (hε_one : ε < 1)
    (hk : 0 < k) (hnk : 2 * k + 1 ≤ n) :
    densityParameter ε n k < 1 := by
  sorry

/-- The rounded fingerprint size satisfies the exponential stopping inequality. -/
theorem fingerprintSize_shrink
    {ε : ℝ} {n k : ℕ}
    (hβ : 0 < densityParameter ε n k)
    (hR : 0 < containerThreshold ε n k) :
    Real.exp (-(densityParameter ε n k) * (fingerprintSize ε n k : ℝ)) *
        (vertexCount n k : ℝ) ≤
      (containerThreshold ε n k : ℝ) := by
  sorry

end SimpleGraph.Kneser
