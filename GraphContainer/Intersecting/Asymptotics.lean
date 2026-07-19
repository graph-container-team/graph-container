/-
Copyright (c) 2026 Graph Container formalization team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Graph Container formalization team
-/
module

public import GraphContainer.Intersecting.Container
public import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Uniform asymptotic count of intersecting families

This file keeps the analytic bookkeeping next to the final squeeze argument.  The principal theorem
uses an explicit epsilon formulation of uniformity; sequence and fixed-`k` versions are corollaries.
-/

@[expose] public section

open Filter
open scoped Topology

namespace SimpleGraph.KneserCounting

/-- The auxiliary error parameter used in the container construction. -/
private noncomputable def asymptoticEpsilon (n : ℕ) : ℝ :=
  (Real.sqrt (n : ℝ))⁻¹

/-- The base-two logarithm of the count, normalized by the full-star size. -/
noncomputable def logRatio (n k : ℕ) : ℝ :=
  Real.logb 2 (intersectingFamilyCount n k : ℝ) / (starSize n k : ℝ)

private theorem eventually_fingerprint_le_vertexCount :
    ∀ᶠ n in atTop, ∀ k, InRange n k →
      fingerprintSize (asymptoticEpsilon n) n k ≤ vertexCount n k := by
  sorry

/-- Rounding the container threshold contributes uniformly lower-order error. -/
private theorem eventually_threshold_overhead_le
    {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ n in atTop, ∀ k, InRange n k →
      (containerThreshold (asymptoticEpsilon n) n k : ℝ) - (starSize n k : ℝ) ≤
        δ * (starSize n k : ℝ) := by
  sorry

/-- Fingerprints have uniformly lower-order size. -/
private theorem eventually_fingerprint_overhead_le
    {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ n in atTop, ∀ k, InRange n k →
      (fingerprintSize (asymptoticEpsilon n) n k : ℝ) ≤ δ * (starSize n k : ℝ) := by
  sorry

/-- Choosing a fingerprint contributes a uniformly lower-order logarithmic factor. -/
private theorem eventually_fingerprintChoice_overhead_le
    {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ n in atTop, ∀ k, InRange n k →
      Real.logb 2
          ((vertexCount n k).choose
            (fingerprintSize (asymptoticEpsilon n) n k) : ℝ) ≤
        δ * (starSize n k : ℝ) := by
  sorry

/-- **Theorem 2.3 (uniform form).**

The normalized logarithm tends to one uniformly for `3 ≤ k` and `2 * k + 1 ≤ n`.
-/
theorem intersectingFamilyCount_logRatio_tendstoUniformly :
    ∀ δ > 0, ∀ᶠ n in atTop, ∀ k, InRange n k → |logRatio n k - 1| < δ := by
  intro δ hδ
  have hR := eventually_threshold_overhead_le hδ
  have hq := eventually_fingerprint_overhead_le hδ
  have hchoice := eventually_fingerprintChoice_overhead_le hδ
  have hvalid := eventually_fingerprint_le_vertexCount
  -- Use `pow_starSize_le_intersectingFamilyCount` for the lower bound and
  -- `intersectingFamilyCount_le` for the upper bound, then squeeze.
  sorry

/-- Sequence formulation of the uniform asymptotic theorem. -/
theorem intersectingFamilyCount_logRatio_tendsto_one
    (k : ℕ → ℕ) (hk : ∀ᶠ n in atTop, InRange n (k n)) :
    Tendsto (fun n ↦ logRatio n (k n)) atTop (𝓝 1) := by
  rw [Metric.tendsto_nhds]
  intro δ hδ
  filter_upwards [intersectingFamilyCount_logRatio_tendstoUniformly δ hδ, hk] with n hU hn
  simpa [Real.dist_eq] using hU (k n) hn

/-- Fixed-`k` formulation, obtained as a special case of the sequence theorem. -/
theorem intersectingFamilyCount_logRatio_tendsto_one_fixed
    {k : ℕ} (hk : 3 ≤ k) :
    Tendsto (fun n ↦ logRatio n k) atTop (𝓝 1) := by
  apply intersectingFamilyCount_logRatio_tendsto_one (fun _ ↦ k)
  filter_upwards [eventually_ge_atTop (2 * k + 1)] with n hn
  exact ⟨hk, hn⟩

end SimpleGraph.KneserCounting
