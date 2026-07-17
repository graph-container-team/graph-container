/-
Copyright (c) 2026 Graph Container formalization team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Graph Container formalization team
-/
module

public import GraphContainer.Basic
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
  sorry

theorem degreeWithin_le_maxDegreeVertex (A : Finset V) (hA : A.Nonempty) (v : V)
    (hv : v ∈ A) :
    degreeWithin G A v ≤ degreeWithin G A (maxDegreeVertex G A hA) := by
  sorry

/-- The degree within a finset agrees with degree in the corresponding induced graph. -/
theorem degreeWithin_eq_degree_induce (A : Finset V) (v : A) :
    degreeWithin G A v = (G.induce (A : Set V)).degree v := by
  sorry

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

@[simp]
theorem maxDegreeOrder_empty : maxDegreeOrder G ∅ = [] := by
  sorry

theorem maxDegreeOrder_eq_nil_iff (A : Finset V) :
    maxDegreeOrder G A = [] ↔ A = ∅ := by
  sorry

theorem maxDegreeOrder_nodup (A : Finset V) :
    (maxDegreeOrder G A).Nodup := by
  sorry

@[simp]
theorem maxDegreeOrder_toFinset (A : Finset V) :
    (maxDegreeOrder G A).toFinset = A := by
  sorry

@[simp]
theorem length_maxDegreeOrder (A : Finset V) :
    (maxDegreeOrder G A).length = #A := by
  sorry

/-- Every vertex is maximal when it is reached in the max-degree ordering. -/
theorem degreeWithin_le_of_maxDegreeOrder_eq_append_cons
    (A : Finset V) {before suffix : List V} {v w : V}
    (horder : maxDegreeOrder G A = before ++ v :: suffix)
    (hw : w ∈ (v :: suffix).toFinset) :
    degreeWithin G (v :: suffix).toFinset w ≤
      degreeWithin G (v :: suffix).toFinset v := by
  sorry

end SimpleGraph.Container
