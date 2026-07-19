/-
Copyright (c) 2026 Graph Container formalization team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Graph Container formalization team
-/
module

public import GraphContainer.Intersecting.Asymptotics

/-!
# The number of intersecting uniform families

This file contains the sole public mathematical target of the second formalization phase:
Theorem 2.3 from the supplied PDF.
-/

@[expose] public section

open Filter
open scoped Topology

namespace SimpleGraph.Kneser

/-- **Theorem 2.3 (Balogh-Das-Delcourt-Liu-Sharifzadeh).**

Uniformly for every sequence `k = k(n)` satisfying `3 ≤ k` and `2 * k + 1 ≤ n` eventually, the
number of intersecting `k`-uniform families is
`2 ^ ((1 + o(1)) * (n - 1).choose (k - 1))`.

The displayed limit is the precise meaning of the exponent notation in the PDF.
-/
theorem intersectingFamilyCount_log_ratio_tendsto_one
    (k : ℕ → ℕ)
    (hk : ∀ᶠ n in atTop, 3 ≤ k n ∧ 2 * k n + 1 ≤ n) :
    Tendsto
      (fun n ↦
        Real.log (intersectingFamilyCount n (k n) : ℝ) /
          (((n - 1).choose (k n - 1) : ℝ) * Real.log 2))
      atTop (𝓝 1) := by
  have hupper :
      Tendsto (fun n ↦ 1 + containerOverhead n (k n)) atTop (𝓝 (1 : ℝ)) := by
    simpa using
      (tendsto_const_nhds.add (containerOverhead_tendsto_zero k hk))
  have hsqueeze :
      Tendsto (fun n ↦ normalizedLogCount n (k n)) atTop (𝓝 (1 : ℝ)) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le'
      tendsto_const_nhds hupper
      (eventually_one_le_normalizedLogCount k hk)
      (eventually_normalizedLogCount_le k hk)
  simpa [normalizedLogCount, starSize] using hsqueeze

end SimpleGraph.Kneser
