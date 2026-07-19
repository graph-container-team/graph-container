/-
Copyright (c) 2026 Graph Container formalization team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Graph Container formalization team
-/
module

public import Mathlib.Combinatorics.SetFamily.Intersecting
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Data.Set.PowersetCard

/-!
# Kneser graphs and intersecting families

This file contains the finite combinatorial objects used in the proof of the asymptotic counting
theorem.  Spectral estimates, graph containers, and asymptotics are deliberately kept out of this
file.
-/

@[expose] public section

open Finset

namespace SimpleGraph.KneserCounting

/-- The type of `k`-subsets of `Fin n`. -/
abbrev Vertex (n k : ℕ) := Set.powersetCard (Fin n) k

/-- The number of vertices of the Kneser graph. -/
def vertexCount (n k : ℕ) : ℕ := n.choose k

/-- The size of a full star. -/
def starSize (n k : ℕ) : ℕ := (n - 1).choose (k - 1)

/-- The degree of the Kneser graph. -/
def regularDegree (n k : ℕ) : ℕ := (n - k).choose k

/-- The range in which the asymptotic counting theorem is stated. -/
def InRange (n k : ℕ) : Prop := 3 ≤ k ∧ 2 * k + 1 ≤ n

/-- There are `n.choose k` vertices. -/
theorem card_vertex (n k : ℕ) : Fintype.card (Vertex n k) = vertexCount n k := by
  rw [Fintype.card_eq_nat_card, Set.powersetCard.card, Nat.card_fin]
  rfl

/-- The Kneser graph on the `k`-subsets of `Fin n`. -/
def graph (n k : ℕ) : SimpleGraph (Vertex n k) where
  Adj A B := A ≠ B ∧ Disjoint (A : Finset (Fin n)) (B : Finset (Fin n))
  symm.symm _ _ h := ⟨h.1.symm, h.2.symm⟩
  loopless.irrefl _ h := h.1 rfl

instance graph.instDecidableRelAdj (n k : ℕ) : DecidableRel (graph n k).Adj :=
  inferInstanceAs (DecidableRel fun A B : Vertex n k ↦
    A ≠ B ∧ Disjoint (A : Finset (Fin n)) (B : Finset (Fin n)))

@[simp] theorem graph_adj_iff {A B : Vertex n k} :
    (graph n k).Adj A B ↔
      A ≠ B ∧ Disjoint (A : Finset (Fin n)) (B : Finset (Fin n)) :=
  Iff.rfl

/-- For positive `k`, adjacency is equivalent to disjointness. -/
theorem graph_adj_iff_disjoint (hk : 0 < k) {A B : Vertex n k} :
    (graph n k).Adj A B ↔ Disjoint (A : Finset (Fin n)) (B : Finset (Fin n)) := by
  sorry

/-- Forget the cardinality certificates carried by a uniform family. -/
def underlyingFamily (𝒜 : Finset (Vertex n k)) : Set (Finset (Fin n)) :=
  (fun A : Vertex n k ↦ (A : Finset (Fin n))) '' (𝒜 : Set (Vertex n k))

/-- The canonical mathlib predicate for an intersecting uniform family. -/
def IsIntersecting (𝒜 : Finset (Vertex n k)) : Prop :=
  (underlyingFamily 𝒜).Intersecting

/-- Intersecting families are precisely independent sets in the Kneser graph. -/
theorem isIntersecting_iff_isIndepSet (hk : 0 < k) (𝒜 : Finset (Vertex n k)) :
    IsIntersecting 𝒜 ↔ (graph n k).IsIndepSet 𝒜 := by
  sorry

/-- The finite collection of all intersecting `k`-uniform families on `Fin n`. -/
noncomputable def intersectingFamilies (n k : ℕ) : Finset (Finset (Vertex n k)) := by
  classical
  exact Finset.univ.filter IsIntersecting

@[simp] theorem mem_intersectingFamilies {𝒜 : Finset (Vertex n k)} :
    𝒜 ∈ intersectingFamilies n k ↔ IsIntersecting 𝒜 := by
  classical
  simp [intersectingFamilies]

/-- The number of intersecting `k`-uniform families on `Fin n`. -/
noncomputable def intersectingFamilyCount (n k : ℕ) : ℕ :=
  #(intersectingFamilies n k)

/-- The empty family shows that the counting function is positive. -/
theorem intersectingFamilyCount_pos (n k : ℕ) : 0 < intersectingFamilyCount n k := by
  sorry

/-- The full star through `i`. -/
def star (i : Fin n) (k : ℕ) : Finset (Vertex n k) :=
  Finset.univ.filter fun A ↦ i ∈ (A : Finset (Fin n))

/-- A full star has size `choose (n - 1) (k - 1)`. -/
theorem card_star (i : Fin n) {k : ℕ} (hk : 0 < k) :
    #(star i k) = starSize n k := by
  sorry

/-- Subfamilies of a full star give the elementary lower bound. -/
theorem pow_starSize_le_intersectingFamilyCount
    {n k : ℕ} (hn : 0 < n) (hk : 0 < k) :
    2 ^ starSize n k ≤ intersectingFamilyCount n k := by
  sorry

end SimpleGraph.KneserCounting
