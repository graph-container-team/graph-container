/-
Copyright (c) 2026 Graph Container formalization team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Graph Container formalization team
-/
module
public import GraphContainer.Basic
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Finset.Sort

/-!
# Max-degree ordering

This file defines a deterministic max-degree ordering.  At every stage a vertex of maximum degree
in the graph induced by the remaining vertices is chosen.  `Classical.choose` provides stable
tie-breaking without placing an arbitrary order on the public vertex type.

This is work package 1 in `IMPLEMENTATION.md`.
-/

@[expose] public section

open Finset

namespace SimpleGraph.Container

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The number of neighbors of `v` that lie in `A`. -/
def degreeWithin (A : Finset V) (v : V) : ℕ :=
  #(G.neighborFinset v ∩ A)

/-- A deterministically chosen vertex of maximum degree inside a nonempty active set. -/
noncomputable def maxDegreeVertex (A : Finset V) (hA : A.Nonempty) : V :=
  (Finset.exists_max_image A (degreeWithin G A) hA).choose

theorem maxDegreeVertex_mem (A : Finset V) (hA : A.Nonempty) :
    maxDegreeVertex G A hA ∈ A := by
      exact (Finset.exists_max_image A (degreeWithin G A) hA).choose_spec.1

theorem degreeWithin_le_maxDegreeVertex (A : Finset V) (hA : A.Nonempty) (v : V)
    (hv : v ∈ A) :
    degreeWithin G A v ≤ degreeWithin G A (maxDegreeVertex G A hA) := by
      exact (Finset.exists_max_image A (degreeWithin G A) hA).choose_spec.2 v hv

/-- The degree within a finset agrees with degree in the corresponding induced graph. -/
theorem degreeWithin_eq_degree_induce (A : Finset V) (v : A) :
    degreeWithin G A v = (G.induce (A : Set V)).degree v := by
  calc
    degreeWithin G A v = #(G.neighborFinset v ∩ A) := rfl
    _ = #(((G.induce (A : Set V)).neighborFinset v).map (.subtype (· ∈ (A : Set V)))) := by
      congr 1
      ext x
      simp
    _ = (G.induce (A : Set V)).degree v := Finset.card_map _

/-- Iteratively remove a maximum-degree vertex. -/
noncomputable def maxDegreeOrder (A : Finset V) : List V :=
  if hA : A.Nonempty then
    let v := maxDegreeVertex G A hA
    v :: maxDegreeOrder (A.erase v)
  else
    []
termination_by A.card
decreasing_by
  exact Finset.card_erase_lt_of_mem (maxDegreeVertex_mem G A hA)

theorem maxDegreeOrder_empty : maxDegreeOrder G ∅ = [] := by
  rw [maxDegreeOrder]
  exact dif_neg Finset.not_nonempty_empty

theorem maxDegreeOrder_eq_nil_iff (A : Finset V) :
    maxDegreeOrder G A = [] ↔ A = ∅ := by
    constructor
    · intro h
      by_contra hA
      have hA' : A.Nonempty := Finset.nonempty_iff_ne_empty.mpr hA
      rw [maxDegreeOrder, dif_pos hA'] at h
      change maxDegreeVertex G A hA' ::
        maxDegreeOrder G (A.erase (maxDegreeVertex G A hA')) = [] at h
      exact (List.cons_ne_nil _ _) h
    · rintro rfl
      exact maxDegreeOrder_empty G

private theorem maxDegreeOrder_nodup_and_toFinset (A : Finset V) :
    (maxDegreeOrder G A).Nodup ∧
      (maxDegreeOrder G A).toFinset = A := by
  classical
  refine Finset.strongInductionOn A (fun A ih => ?_)
  by_cases hA : A.Nonempty
  · rw [maxDegreeOrder, dif_pos hA]
    let v := maxDegreeVertex G A hA
    have hv : v ∈ A := maxDegreeVertex_mem G A hA
    have htail := ih (A.erase v) (Finset.erase_ssubset hv)
    constructor
    · apply List.nodup_cons.mpr
      constructor
      · intro hmem
        have hmem' : v ∈ (maxDegreeOrder G (A.erase v)).toFinset :=
          List.mem_toFinset.mpr hmem
        rw [htail.2] at hmem'
        exact (Finset.mem_erase.mp hmem').1 rfl
      · exact htail.1
    · rw [List.toFinset_cons, htail.2]
      exact Finset.insert_erase hv
  · rw [maxDegreeOrder, dif_neg hA, List.toFinset_nil]
    exact ⟨List.nodup_nil, (not_nonempty_iff_eq_empty.mp hA).symm⟩

theorem maxDegreeOrder_nodup (A : Finset V) :
    (maxDegreeOrder G A).Nodup := by
  exact (maxDegreeOrder_nodup_and_toFinset G A).1

@[simp]
theorem maxDegreeOrder_toFinset (A : Finset V) :
    (maxDegreeOrder G A).toFinset = A := by
  exact (maxDegreeOrder_nodup_and_toFinset G A).2

@[simp]
theorem length_maxDegreeOrder (A : Finset V) :
    (maxDegreeOrder G A).length = #A := by
  have h := maxDegreeOrder_nodup_and_toFinset G A
  calc
    (maxDegreeOrder G A).length = #(maxDegreeOrder G A).toFinset :=
      (List.toFinset_card_of_nodup h.1).symm
    _ = #A := by rw [h.2]

/-- Every vertex is maximal when it is reached in the max-degree ordering. -/
theorem degreeWithin_le_of_maxDegreeOrder_eq_append_cons
    (A : Finset V) {before suffix : List V} {v w : V}
    (horder : maxDegreeOrder G A = before ++ v :: suffix)
    (hw : w ∈ (v :: suffix).toFinset) :
    degreeWithin G (v :: suffix).toFinset w ≤
      degreeWithin G (v :: suffix).toFinset v := by
  induction before generalizing A with
  | nil =>
    have hA : A.Nonempty := by
      by_contra hA
      have hzero : A = ∅ := not_nonempty_iff_eq_empty.mp hA
      subst A
      rw [maxDegreeOrder_empty] at horder
      simp at horder
    have horder' : maxDegreeOrder G A = v :: suffix := by
      simpa only [List.nil_append] using horder
    have hset : (v :: suffix).toFinset = A := by
      rw [← horder']
      exact (maxDegreeOrder_nodup_and_toFinset G A).2
    rw [maxDegreeOrder, dif_pos hA] at horder'
    dsimp only at horder'
    injection horder' with hhead htail
    have hwA : w ∈ A := by
      rw [← hset]
      exact hw
    have hmax := degreeWithin_le_maxDegreeVertex G A hA w hwA
    simpa only [hset, hhead] using hmax
  | cons a before ih =>
    have hA : A.Nonempty := by
      by_contra hA
      have hzero : A = ∅ := not_nonempty_iff_eq_empty.mp hA
      subst A
      rw [maxDegreeOrder_empty] at horder
      simp at horder
    have horder' : maxDegreeOrder G A = a :: (before ++ v :: suffix) := by
      simpa only [List.cons_append] using horder
    rw [maxDegreeOrder, dif_pos hA] at horder'
    dsimp only at horder'
    injection horder' with hhead htail
    exact ih (A.erase (maxDegreeVertex G A hA)) htail

end SimpleGraph.Container
