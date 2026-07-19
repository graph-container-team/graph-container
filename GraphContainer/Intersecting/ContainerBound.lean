/-
Copyright (c) 2026 Graph Container formalization team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Graph Container formalization team
-/
module

public import GraphContainer.Family
public import GraphContainer.Intersecting.LocalDensity

/-!
# The finite container bound behind Theorem 2.3

The public theorem is asymptotic, but its proof passes through an explicit finite inequality. This
file counts all subsets of every container and specializes that inequality to the Kneser graph.
-/

@[expose] public section

open Finset

namespace SimpleGraph.Kneser

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- All independent vertex sets of a finite graph. This is an internal counting device for
Theorem 2.3, unlike `SimpleGraph.indepSetFinset`, which fixes their cardinality. -/
def allIndependentSetFinset (G : SimpleGraph V) [DecidableRel G.Adj] :
    Finset (Finset V) :=
  Finset.univ.filter fun I ↦ G.IsIndepSet I

@[simp] theorem mem_allIndependentSetFinset
    (G : SimpleGraph V) [DecidableRel G.Adj] {I : Finset V} :
    I ∈ allIndependentSetFinset G ↔ G.IsIndepSet I := by
  simp [allIndependentSetFinset]

/-- A container family bounds the total number of independent sets. -/
theorem card_allIndependentSetFinset_le
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {β : ℝ} {R q : ℕ} (h : Container.Hypotheses G β R q) :
    #(allIndependentSetFinset G) ≤
      (Fintype.card V).choose q * 2 ^ (R + q) := by
  sorry

/-- The finite upper bound obtained by applying the graph container theorem to the Kneser graph. -/
theorem intersectingFamilyCount_le_containerBound
    {ε : ℝ} {n k : ℕ}
    (hk : 0 < k)
    (h : Container.Hypotheses (graph n k)
      (densityParameter ε n k)
      (containerThreshold ε n k)
      (fingerprintSize ε n k)) :
    intersectingFamilyCount n k ≤
      (vertexCount n k).choose (fingerprintSize ε n k) *
        2 ^ (containerThreshold ε n k + fingerprintSize ε n k) := by
  sorry

/-- The complete finite data needed to invoke the preceding bound. -/
structure AdmissibleContainerParameters (ε : ℝ) (n k : ℕ) : Prop where
  epsilon_pos : 0 < ε
  epsilon_lt_one : ε < 1
  k_pos : 0 < k
  range : 2 * k + 1 ≤ n
  fingerprint_le : fingerprintSize ε n k ≤ vertexCount n k

/-- Admissible rounded parameters satisfy all hypotheses of the graph container theorem. -/
theorem containerHypotheses
    {ε : ℝ} {n k : ℕ} (h : AdmissibleContainerParameters ε n k) :
    Container.Hypotheses (graph n k)
      (densityParameter ε n k)
      (containerThreshold ε n k)
      (fingerprintSize ε n k) := by
  sorry

/-- A directly usable finite upper bound for admissible parameters. -/
theorem intersectingFamilyCount_le
    {ε : ℝ} {n k : ℕ} (h : AdmissibleContainerParameters ε n k) :
    intersectingFamilyCount n k ≤
      (vertexCount n k).choose (fingerprintSize ε n k) *
        2 ^ (containerThreshold ε n k + fingerprintSize ε n k) := by
  sorry

end SimpleGraph.Kneser
