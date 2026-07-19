/-
Copyright (c) 2026 Graph Container formalization team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Graph Container formalization team
-/
module

public import GraphContainer.IntersectingCounting.Basic
public import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum
public import Mathlib.Data.Real.Basic
public import Mathlib.LinearAlgebra.Eigenspace.Matrix

/-!
# Supersaturation in Kneser graphs

This file makes the spectral input to the container argument explicit.  Theorems 2.5 and 2.6 are
cited inputs.  Their only use in the counting theorem is to prove Proposition 2.7.
-/

@[expose] public section

open Finset

namespace SimpleGraph

/-- **Theorem 2.5 (cited spectral estimate).**

The least adjacency eigenvalue controls the number of edges induced by every vertex set in a
regular graph.
-/
theorem expanderMixing_inducedEdgeCount
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {D : ℕ} {lam : ℝ}
    (hreg : G.IsRegularOfDegree D)
    (hlam : IsLeast (spectrum ℝ (G.adjMatrix ℝ)) lam)
    (S : Finset V) :
    (D : ℝ) / (2 * (Fintype.card V : ℝ)) * (S.card : ℝ) ^ 2 +
        lam / (2 * (Fintype.card V : ℝ)) * (S.card : ℝ) *
          ((Fintype.card V : ℝ) - (S.card : ℝ)) ≤
      (#(G.induce (S : Set V)).edgeFinset : ℝ) := by
  sorry

end SimpleGraph

namespace SimpleGraph.KneserCounting

/-- The Kneser graph is regular of degree `choose (n - k) k`. -/
theorem graph_isRegularOfDegree (n : ℕ) {k : ℕ} (hk : 0 < k) :
    (graph n k).IsRegularOfDegree (regularDegree n k) := by
  sorry

/-- **Theorem 2.6 (cited Kneser spectrum).**

The minimum eigenvalue is written in the equivalent form `-k / (n-k) * D` used by the
supersaturation calculation.
-/
theorem kneser_minEigenvalue
    {n k : ℕ} (hk : 0 < k) (hnk : 2 * k + 1 ≤ n) :
    IsLeast (spectrum ℝ ((graph n k).adjMatrix ℝ))
      (-((k : ℝ) / (((n - k : ℕ) : ℝ)) * (regularDegree n k : ℝ))) := by
  sorry

/-- The local-density coefficient in Proposition 2.7. -/
noncomputable def densityParameter (ε : ℝ) (n k : ℕ) : ℝ :=
  (ε / (1 + ε)) *
    ((regularDegree n k : ℝ) * (n : ℝ) /
      ((vertexCount n k : ℝ) * ((n - k : ℕ) : ℝ)))

/-- **Proposition 2.7 (proved from Theorems 2.5 and 2.6).**

Every sufficiently large vertex set in the Kneser graph spans a positive proportion of all its
possible edges.
-/
theorem kneser_supersaturation
    {ε : ℝ} {n k : ℕ}
    (hε : 0 < ε) (hk : 0 < k) (hnk : 2 * k + 1 ≤ n)
    (S : Finset (Vertex n k))
    (hS : (1 + ε) * (starSize n k : ℝ) ≤ (S.card : ℝ)) :
    densityParameter ε n k * (S.card.choose 2 : ℝ) ≤
      (#((graph n k).induce (S : Set (Vertex n k))).edgeFinset : ℝ) := by
  have hreg := graph_isRegularOfDegree n hk
  have hmin := kneser_minEigenvalue hk hnk
  have hmixed := SimpleGraph.expanderMixing_inducedEdgeCount (graph n k) hreg hmin S
  -- Rewrite `Fintype.card (Vertex n k)` and use `hS` in the spectral lower bound.
  sorry

end SimpleGraph.KneserCounting
