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

variable (n k : ℕ)

/-- The type of `k`-subsets of `Fin n`. -/
abbrev Vertex := Set.powersetCard (Fin n) k

/-- The number of vertices of the Kneser graph. -/
def vertexCount : ℕ := n.choose k

/-- The size of a full star. -/
def starSize : ℕ := (n - 1).choose (k - 1)

/-- The degree of the Kneser graph. -/
def regularDegree : ℕ := (n - k).choose k

/-- The range in which the asymptotic counting theorem is stated. -/
def InRange : Prop := 3 ≤ k ∧ 2 * k + 1 ≤ n

/-- There are `n.choose k` vertices. -/
theorem card_vertex : Fintype.card (Vertex n k) = vertexCount n k := by
  rw [Fintype.card_eq_nat_card, Set.powersetCard.card, Nat.card_fin]
  rfl

/-- The Kneser graph on the `k`-subsets of `Fin n`. -/
def graph : SimpleGraph (Vertex n k) where
  Adj A B := A ≠ B ∧ Disjoint (A : Finset (Fin n)) (B : Finset (Fin n))
  symm.symm _ _ h := ⟨h.1.symm, h.2.symm⟩
  loopless.irrefl _ h := h.1 rfl

instance graph.instDecidableRelAdj : DecidableRel (graph n k).Adj :=
  inferInstanceAs (DecidableRel fun A B : Vertex n k ↦
    A ≠ B ∧ Disjoint (A : Finset (Fin n)) (B : Finset (Fin n)))

@[simp] theorem graph_adj_iff {A B : Vertex n k} :
    (graph n k).Adj A B ↔
      A ≠ B ∧ Disjoint (A : Finset (Fin n)) (B : Finset (Fin n)) :=
  Iff.rfl

/-- For positive `k`, adjacency is equivalent to disjointness. -/
theorem graph_adj_iff_disjoint (hk : 0 < k) {A B : Vertex n k} :
    (graph n k).Adj A B ↔ Disjoint (A : Finset (Fin n)) (B : Finset (Fin n)) := by
  rw [graph_adj_iff]
  refine and_iff_right_of_imp fun hdisjoint hAB ↦ ?_
  subst B
  have hAempty : (A : Finset (Fin n)) = ∅ :=
    Finset.disjoint_self_iff_empty (A : Finset (Fin n)) |>.mp hdisjoint
  have hcard : k = 0 := by
    simpa [hAempty] using (Set.powersetCard.card_eq A).symm
  omega

/-- Forget the cardinality certificates carried by a uniform family. -/
def underlyingFamily (𝒜 : Finset (Vertex n k)) : Set (Finset (Fin n)) :=
  (fun A : Vertex n k ↦ (A : Finset (Fin n))) '' (𝒜 : Set (Vertex n k))

/-- The canonical mathlib predicate for an intersecting uniform family. -/
def IsIntersecting (𝒜 : Finset (Vertex n k)) : Prop :=
  (underlyingFamily n k 𝒜).Intersecting

/-- Intersecting families are precisely independent sets in the Kneser graph. -/
theorem isIntersecting_iff_isIndepSet (hk : 0 < k) (𝒜 : Finset (Vertex n k)) :
    IsIntersecting n k 𝒜 ↔ (graph n k).IsIndepSet 𝒜 := by
  rw [SimpleGraph.isIndepSet_iff]
  constructor
  · intro h A hA B hB _hAB hadj
    apply h
    · exact ⟨A, hA, rfl⟩
    · exact ⟨B, hB, rfl⟩
    · exact (graph_adj_iff_disjoint hk).mp hadj
  · intro h
    rintro A ⟨A', hA', rfl⟩ B ⟨B', hB', rfl⟩ hdisjoint
    have hadj : (graph n k).Adj A' B' :=
      (graph_adj_iff_disjoint hk).mpr hdisjoint
    exact (h hA' hB' (graph_adj_iff.mp hadj).1) hadj


/-- The finite collection of all intersecting `k`-uniform families on `Fin n`. -/
noncomputable def intersectingFamilies (n k : ℕ) : Finset (Finset (Vertex n k)) := by
  classical
  exact Finset.univ.filter (IsIntersecting n k)

@[simp] theorem mem_intersectingFamilies {𝒜 : Finset (Vertex n k)} :
    𝒜 ∈ intersectingFamilies n k ↔ IsIntersecting n k 𝒜 := by
  classical
  simp [intersectingFamilies]

/-- The number of intersecting `k`-uniform families on `Fin n`. -/
noncomputable def intersectingFamilyCount (n k : ℕ) : ℕ :=
  #(intersectingFamilies n k)

/-- The empty family shows that the counting function is positive. -/
theorem intersectingFamilyCount_pos (n k : ℕ) : 0 < intersectingFamilyCount n k := by
  classical
  rw [intersectingFamilyCount, Finset.card_pos]
  refine ⟨∅, ?_⟩
  rw [mem_intersectingFamilies, IsIntersecting, underlyingFamily]
  simpa using Set.intersecting_empty

/-- The full star through `i`. -/
def star (i : Fin n) (k : ℕ) : Finset (Vertex n k) :=
  Finset.univ.filter fun A ↦ i ∈ (A : Finset (Fin n))

/-- A full star has size `choose (n - 1) (k - 1)`. -/
theorem card_star (i : Fin n) {k : ℕ} (hk : 0 < k) :
    #(star n i k) = starSize n k := by
  classical
  let valEmbedding : Vertex n k ↪ Finset (Fin n) :=
    ⟨fun A ↦ (A : Finset (Fin n)), fun _ _ h ↦ Subtype.ext h⟩
  have hmap :
      (star n i k).map valEmbedding =
        ((Finset.univ : Finset (Fin n)).powersetCard k).filter (i ∈ ·) := by
    ext A
    simp [star, valEmbedding, Finset.mem_powersetCard, and_comm]
  calc
    #(star n i k) = #((star n i k).map valEmbedding) := (Finset.card_map _).symm
    _ = #(((Finset.univ : Finset (Fin n)).powersetCard k).filter (i ∈ ·)) := by
      rw [hmap]
    _ = #(((Finset.univ : Finset (Fin n)).powersetCard k).filter ({i} ⊆ ·)) := by
      congr 2
      ext A
      simp
    _ = Nat.choose (#(Finset.univ : Finset (Fin n)) - #{i}) (k - #{i}) :=
      Finset.card_filter_powersetCard_subset {i} Finset.univ k
        (Finset.subset_univ _) (by rw [Finset.card_singleton]; exact hk)
    _ = starSize n k := by simp [starSize]


/-- Subfamilies of a full star give the elementary lower bound. -/
theorem pow_starSize_le_intersectingFamilyCount
    {n k : ℕ} (hn : 0 < n) (hk : 0 < k) :
    2 ^ starSize n k ≤ intersectingFamilyCount n k := by
  classical
  let i : Fin n := ⟨0, hn⟩
  have hsubset : (star i k).powerset ⊆ intersectingFamilies n k := by
    intro 𝒜 h𝒜
    rw [mem_intersectingFamilies, IsIntersecting, underlyingFamily]
    rintro A ⟨A', hA', rfl⟩ B ⟨B', hB', rfl⟩
    have h𝒜star : 𝒜 ⊆ star i k := Finset.mem_powerset.mp h𝒜
    have hiA : i ∈ (A' : Finset (Fin n)) :=
      (Finset.mem_filter.mp (h𝒜star hA')).2
    have hiB : i ∈ (B' : Finset (Fin n)) :=
      (Finset.mem_filter.mp (h𝒜star hB')).2
    exact Finset.not_disjoint_iff.mpr ⟨i, hiA, hiB⟩
  calc
    2 ^ starSize n k = #((star i k).powerset) := by
      rw [Finset.card_powerset, card_star i hk]
    _ ≤ #(intersectingFamilies n k) := Finset.card_le_card hsubset
    _ = intersectingFamilyCount n k := rfl

end SimpleGraph.KneserCounting
