/-
Copyright (c) 2026 Graph Container formalization team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Graph Container formalization team
-/
module

public import GraphContainer.Intersecting.ContainerBound
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Order.Filter.AtTopBot.Floor

/-!
# Uniform parameter estimates for Theorem 2.3

This file controls the rounded graph-container parameters uniformly over every sequence
`k = k(n)` that is eventually in the range `3 ≤ k` and `2 * k + 1 ≤ n`. We use
`ε(n) = 1 / sqrt n`.
-/

@[expose] public section

open Filter
open scoped Topology

namespace SimpleGraph.Kneser

/-- A concrete error parameter tending to zero uniformly in the permitted values of `k`. -/
noncomputable def asymptoticEpsilon (n : ℕ) : ℝ :=
  (Real.sqrt (n : ℝ))⁻¹

/-- The admissible range forces the full-star size to diverge uniformly. -/
theorem starSize_tendsto_atTop
    (k : ℕ → ℕ)
    (hk : ∀ᶠ n in atTop, 3 ≤ k n ∧ 2 * k n + 1 ≤ n) :
    Tendsto (fun n ↦ starSize n (k n)) atTop atTop := by
  sorry

/-- The chosen auxiliary parameter tends to zero. -/
theorem asymptoticEpsilon_tendsto_zero :
    Tendsto asymptoticEpsilon atTop (𝓝 0) := by
  sorry

/-- The rounded parameters are eventually valid graph-container parameters, uniformly in `k`. -/
theorem eventually_admissibleContainerParameters
    (k : ℕ → ℕ)
    (hk : ∀ᶠ n in atTop, 3 ≤ k n ∧ 2 * k n + 1 ≤ n) :
    ∀ᶠ n in atTop,
      AdmissibleContainerParameters (asymptoticEpsilon n) n (k n) := by
  sorry

/-- Rounding the threshold changes the main exponent by only a lower-order term. -/
theorem threshold_error_isLittleO
    (k : ℕ → ℕ)
    (hk : ∀ᶠ n in atTop, 3 ≤ k n ∧ 2 * k n + 1 ≤ n) :
    (fun n ↦
      (containerThreshold (asymptoticEpsilon n) n (k n) : ℝ) -
        (starSize n (k n) : ℝ)) =o[atTop]
      (fun n ↦ (starSize n (k n) : ℝ)) := by
  sorry

/-- Fingerprints have lower-order size compared with a full star. -/
theorem fingerprintSize_isLittleO
    (k : ℕ → ℕ)
    (hk : ∀ᶠ n in atTop, 3 ≤ k n ∧ 2 * k n + 1 ≤ n) :
    (fun n ↦ (fingerprintSize (asymptoticEpsilon n) n (k n) : ℝ)) =o[atTop]
      (fun n ↦ (starSize n (k n) : ℝ)) := by
  sorry

end SimpleGraph.Kneser
