/-
Copyright (c) 2026 Graph Container formalization team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Graph Container formalization team
-/
module

public import GraphContainer.Family
public import GraphContainer.Intersecting.Supersaturation
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Applying the graph-container theorem

Proposition 2.7 is converted into `Container.IsLocallyDense`, after which the general graph
container theorem gives the finite upper bound used in the asymptotic argument.
-/

@[expose] public section

open Finset

namespace SimpleGraph.KneserCounting

/-- The rounded container threshold corresponding to `(1 + ε) * starSize n k`. -/
noncomputable def containerThreshold (ε : ℝ) (n k : ℕ) : ℕ :=
  ⌈(1 + ε) * (starSize n k : ℝ)⌉₊

/-- The rounded fingerprint size used in the graph-container theorem. -/
noncomputable def fingerprintSize (ε : ℝ) (n k : ℕ) : ℕ :=
  ⌈(densityParameter ε n k)⁻¹ *
      Real.log ((vertexCount n k : ℝ) / (containerThreshold ε n k : ℝ))⌉₊

/-- Proposition 2.7 supplies precisely the local-density hypothesis required by the container
theorem. -/
theorem kneser_isLocallyDense
    {ε : ℝ} {n k : ℕ}
    (hε : 0 < ε) (hk : 0 < k) (hnk : 2 * k + 1 ≤ n) :
    Container.IsLocallyDense (graph n k)
      (densityParameter ε n k) (containerThreshold ε n k) := by
  intro S hS
  apply kneser_supersaturation hε hk hnk S
  exact Nat.ceil_le.mp hS

/-- The rounded parameters satisfy all hypotheses of the graph-container theorem.

The explicit `fingerprintSize ≤ vertexCount` assumption records the small correction missing from
the informal statement of the container theorem.
-/
theorem kneser_containerHypotheses
    {ε : ℝ} {n k : ℕ}
    (hε : 0 < ε) (hk : 0 < k) (hnk : 2 * k + 1 ≤ n)
    (hq : fingerprintSize ε n k ≤ vertexCount n k) :
    Container.Hypotheses (graph n k)
      (densityParameter ε n k)
      (containerThreshold ε n k)
      (fingerprintSize ε n k) := by
  refine
    { beta_pos := ?_
      beta_lt_one := ?_
      q_le_card := ?_
      locallyDense := kneser_isLocallyDense hε hk hnk
      shrink := ?_ }
  · sorry
  · sorry
  · simpa only [card_vertex] using hq
  · sorry

/-- The finite upper bound obtained from any valid set of Kneser-container parameters. -/
theorem intersectingFamilyCount_le
    {β : ℝ} {n k R q : ℕ}
    (hk : 0 < k) (h : Container.Hypotheses (graph n k) β R q) :
    intersectingFamilyCount n k ≤
      (vertexCount n k).choose q * 2 ^ (R + q) := by
  have hcontainers := Container.graph_container_theorem (G := graph n k)
    h
  -- Count all subsets of the containers and use `isIntersecting_iff_isIndepSet`.
  sorry

end SimpleGraph.KneserCounting
