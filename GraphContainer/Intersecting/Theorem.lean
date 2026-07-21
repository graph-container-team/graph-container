/-
Copyright (c) 2026 Graph Container formalization team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Graph Container formalization team
-/
module

public import GraphContainer.Intersecting.Asymptotics

/-!
# Counting intersecting uniform families

This file states the final upper bound in the quantifier form used in the main theorem.  The
auxiliary estimate in `Asymptotics` assumes an error parameter below one and gives a non-strict
bound.  Applying it to a strictly smaller parameter produces the required strict inequality for
every positive `ε`.
-/

@[expose] public section

namespace SimpleGraph.KneserCounting

/-- **Main theorem (upper bound).**

For every positive `ε`, once `n` is sufficiently large, the number of intersecting families of
`k`-subsets of `Fin n` is strictly smaller than
`2 ^ ((1 + 3 * ε) * choose (n - 1) (k - 1))`, uniformly for
`3 ≤ k` and `2 * k + 1 ≤ n`.
-/
theorem eventually_intersectingFamilyCount_lt
    (ε : ℝ) (hε : 0 < ε) :
    ∃ n₀ : ℕ, ∀ n k : ℕ, n₀ ≤ n → 3 ≤ k → 2 * k + 1 ≤ n →
      (intersectingFamilyCount n k : ℝ) <
        Real.rpow 2 ((1 + 3 * ε) * (((n - 1).choose (k - 1) : ℕ) : ℝ)) := by
  let δ : ℝ := min (ε / 2) (1 / 2)
  have hδ : 0 < δ := by
    dsimp [δ]
    rw [lt_min_iff]
    constructor <;> positivity
  have hδone : δ < 1 := by
    calc
      δ ≤ 1 / 2 := min_le_right _ _
      _ < 1 := by norm_num
  have hδε : δ < ε := by
    calc
      δ ≤ ε / 2 := min_le_left _ _
      _ < ε := by linarith
  obtain ⟨n₁, hn₁⟩ := eventually_intersectingFamilyCount_le δ hδ hδone
  refine ⟨n₁ + 1, ?_⟩
  intro n k hn hk hnk
  have hupper := hn₁ n k (by omega) (by omega) hnk
  let M : ℝ := (((n - 1).choose (k - 1) : ℕ) : ℝ)
  have hMnat : 0 < (n - 1).choose (k - 1) := Nat.choose_pos (by omega)
  have hM : 0 < M := by
    dsimp [M]
    exact_mod_cast hMnat
  have hexponent :
      (1 + 3 * δ) * M < (1 + 3 * ε) * M := by
    nlinarith
  have hrpow :
      Real.rpow 2 ((1 + 3 * δ) * M) < Real.rpow 2 ((1 + 3 * ε) * M) :=
    Real.rpow_lt_rpow_of_exponent_lt one_lt_two hexponent
  have hupper' :
      (intersectingFamilyCount n k : ℝ) ≤ Real.rpow 2 ((1 + 3 * δ) * M) := by
    simpa [M, starSize] using hupper
  simpa [M] using hupper'.trans_lt hrpow

end SimpleGraph.KneserCounting
