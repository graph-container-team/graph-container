/-
Copyright (c) 2026 Graph Container formalization team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Graph Container formalization team
-/
module

public import Mathlib.Combinatorics.SetFamily.Intersecting
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Data.Fintype.Powerset

/-!
# Intersecting uniform families

This file contains only the finite objects needed to state Theorem 2.3. A vertex is a `k`-subset
of `Fin n`, and two distinct vertices of the Kneser graph are adjacent when they are disjoint.

`intersectingFamilyCount n k` counts all intersecting families of `k`-subsets, including the empty
family. The subtype representation prevents non-`k`-uniform sets from entering later arguments.
-/

@[expose] public section

open Finset

namespace SimpleGraph.Kneser

variable {n k : ℕ}

/-- The finite type of `k`-subsets of `Fin n`. -/
abbrev Vertex (n k : ℕ) :=
  {A : Finset (Fin n) // A ∈ (Finset.univ : Finset (Fin n)).powersetCard k}

/-- Every Kneser vertex has the prescribed cardinality. -/
@[simp] theorem card_val (A : Vertex n k) : #A.1 = k :=
  (mem_powersetCard.mp A.2).2

/-- There are `n.choose k` vertices in the Kneser graph. -/
@[simp] theorem card_vertex (n k : ℕ) : Fintype.card (Vertex n k) = n.choose k := by
  sorry

/-- The Kneser graph on the `k`-subsets of `Fin n`.

The inequality component makes the definition loopless even for the degenerate case `k = 0`.
For the range of Theorem 2.3, it follows automatically from disjointness.
-/
def graph (n k : ℕ) : SimpleGraph (Vertex n k) where
  Adj A B := A ≠ B ∧ Disjoint A.1 B.1
  symm.symm _A _B h := ⟨h.1.symm, h.2.symm⟩
  loopless.irrefl _A h := h.1 rfl

instance graph.instDecidableRelAdj (n k : ℕ) : DecidableRel (graph n k).Adj :=
  inferInstanceAs
    (DecidableRel fun A B : Vertex n k ↦ A ≠ B ∧ Disjoint A.1 B.1)

noncomputable instance graph.instLocallyFinite (n k : ℕ) : (graph n k).LocallyFinite :=
  fun _ ↦ Fintype.ofFinite _

@[simp] theorem graph_adj_iff {A B : Vertex n k} :
    (graph n k).Adj A B ↔ A ≠ B ∧ Disjoint A.1 B.1 :=
  Iff.rfl

/-- For positive uniformity, Kneser adjacency is exactly disjointness. -/
theorem graph_adj_iff_disjoint (hk : 0 < k) {A B : Vertex n k} :
    (graph n k).Adj A B ↔ Disjoint A.1 B.1 := by
  sorry

/-- A family of Kneser vertices is intersecting when every two of its members meet. -/
def IsIntersectingFamily (𝒜 : Finset (Vertex n k)) : Prop :=
  ∀ ⦃A⦄, A ∈ 𝒜 → ∀ ⦃B⦄, B ∈ 𝒜 → ¬Disjoint A.1 B.1

/-- Forget the cardinality certificates carried by a uniform family. -/
def underlyingFamily (𝒜 : Finset (Vertex n k)) : Finset (Finset (Fin n)) :=
  𝒜.image fun A ↦ A.1

/-- The subtype formulation agrees with mathlib's predicate for intersecting set families. -/
theorem isIntersectingFamily_iff_intersecting (hk : 0 < k) (𝒜 : Finset (Vertex n k)) :
    IsIntersectingFamily 𝒜 ↔
      (↑(underlyingFamily 𝒜) : Set (Finset (Fin n))).Intersecting := by
  sorry

/-- Intersecting uniform families are independent sets in the Kneser graph. -/
theorem isIntersectingFamily_iff_isIndepSet (hk : 0 < k) (𝒜 : Finset (Vertex n k)) :
    IsIntersectingFamily 𝒜 ↔ (graph n k).IsIndepSet 𝒜 := by
  sorry

/-- The finite collection of all intersecting `k`-uniform families on `Fin n`. -/
noncomputable def intersectingFamilyFinset (n k : ℕ) : Finset (Finset (Vertex n k)) := by
  classical
  exact Finset.univ.filter IsIntersectingFamily

@[simp] theorem mem_intersectingFamilyFinset {𝒜 : Finset (Vertex n k)} :
    𝒜 ∈ intersectingFamilyFinset n k ↔ IsIntersectingFamily 𝒜 := by
  classical
  simp [intersectingFamilyFinset]

/-- The number of intersecting `k`-uniform families on `Fin n`. -/
noncomputable def intersectingFamilyCount (n k : ℕ) : ℕ :=
  #(intersectingFamilyFinset n k)

/-- The empty family ensures that the counting function is always positive. -/
theorem intersectingFamilyCount_pos (n k : ℕ) : 0 < intersectingFamilyCount n k := by
  sorry

/-- The full star through a point. -/
def star (i : Fin n) (k : ℕ) : Finset (Vertex n k) :=
  Finset.univ.filter fun A ↦ i ∈ A.1

/-- A full star has the Erdős-Ko-Rado cardinality. -/
theorem card_star (i : Fin n) {k : ℕ} (hk : 0 < k) :
    #(star i k) = (n - 1).choose (k - 1) := by
  sorry

/-- Every subfamily of a full star is intersecting when `k` is positive. -/
theorem powerset_star_subset_intersectingFamilyFinset
    (hk : 0 < k) (i : Fin n) :
    (star i k).powerset ⊆ intersectingFamilyFinset n k := by
  sorry

/-- The star construction gives the lower bound needed for Theorem 2.3. -/
theorem pow_starSize_le_intersectingFamilyCount
    (hk : 0 < k) (i : Fin n) :
    2 ^ ((n - 1).choose (k - 1)) ≤ intersectingFamilyCount n k := by
  sorry

end SimpleGraph.Kneser
