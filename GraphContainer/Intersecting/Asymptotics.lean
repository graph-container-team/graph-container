/-
Copyright (c) 2026 Graph Container formalization team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Graph Container formalization team
-/
module

public import GraphContainer.Intersecting.Parameters

/-!
# Uniform asymptotic estimates for Theorem 2.3

The notation `o(1)` in the PDF is made precise uniformly over every sequence `k = k(n)` that is
eventually in the range `3 ≤ k` and `2 * k + 1 ≤ n`. It combines the separate parameter
estimates into the lower and upper bounds used by the final squeeze argument.
-/

@[expose] public section

open Filter
open scoped Topology

namespace SimpleGraph.Kneser

/-- The logarithmic normalization that precisely represents the exponent in Theorem 2.3. -/
noncomputable def normalizedLogCount (n k : ℕ) : ℝ :=
  Real.log (intersectingFamilyCount n k : ℝ) /
    ((starSize n k : ℝ) * Real.log 2)

/-- The relative excess in the exponent of the finite container upper bound. -/
noncomputable def containerOverhead (n k : ℕ) : ℝ :=
  let ε := asymptoticEpsilon n
  let R := containerThreshold ε n k
  let q := fingerprintSize ε n k
  ((R : ℝ) - (starSize n k : ℝ) + (q : ℝ) +
      Real.logb 2 ((vertexCount n k).choose q : ℝ)) /
    (starSize n k : ℝ)

/-- Choosing a fingerprint contributes only a lower-order logarithmic factor. -/
theorem fingerprintChoiceLog_isLittleO
    (k : ℕ → ℕ)
    (hk : ∀ᶠ n in atTop, 3 ≤ k n ∧ 2 * k n + 1 ≤ n) :
    (fun n ↦
      Real.logb 2
        ((vertexCount n (k n)).choose
          (fingerprintSize (asymptoticEpsilon n) n (k n)) : ℝ)) =o[atTop]
      (fun n ↦ (starSize n (k n) : ℝ)) := by
  sorry

/-- The entire relative overhead in the container bound tends to zero. -/
theorem containerOverhead_tendsto_zero
    (k : ℕ → ℕ)
    (hk : ∀ᶠ n in atTop, 3 ≤ k n ∧ 2 * k n + 1 ≤ n) :
    Tendsto (fun n ↦ containerOverhead n (k n)) atTop (𝓝 0) := by
  sorry

/-- The star construction gives the eventual lower half of the logarithmic squeeze. -/
theorem eventually_one_le_normalizedLogCount
    (k : ℕ → ℕ)
    (hk : ∀ᶠ n in atTop, 3 ≤ k n ∧ 2 * k n + 1 ≤ n) :
    ∀ᶠ n in atTop, 1 ≤ normalizedLogCount n (k n) := by
  sorry

/-- The finite container estimate gives the eventual upper half of the logarithmic squeeze. -/
theorem eventually_normalizedLogCount_le
    (k : ℕ → ℕ)
    (hk : ∀ᶠ n in atTop, 3 ≤ k n ∧ 2 * k n + 1 ≤ n) :
    ∀ᶠ n in atTop,
      normalizedLogCount n (k n) ≤ 1 + containerOverhead n (k n) := by
  sorry

end SimpleGraph.Kneser
