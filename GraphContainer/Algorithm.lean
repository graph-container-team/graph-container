/-
Copyright (c) 2026 Graph Container formalization team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Graph Container formalization team
-/
module

public import GraphContainer.MaxDegreeOrder

/-!
# The Kleitman-Winston graph-container algorithm

For a target independent set `I`, one step orders the active set by iterated maximum degree, selects
the first vertex of that order belonging to `I`, and removes the preceding vertices together with
the selected vertex and all its neighbors.  The selected vertices form the fingerprint.

This is work package 2 in `IMPLEMENTATION.md`.
-/

@[expose] public section

open Finset

namespace SimpleGraph.Container

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The first member of `I` in a list, if one exists. -/
def firstIn (order : List V) (I : Finset V) : Option V :=
  order.find? fun v ↦ v ∈ I

/-- The strict prefix of `order` before the first occurrence of `v`. -/
def beforeVertex (order : List V) (v : V) : List V :=
  order.takeWhile fun w ↦ decide (w ≠ v)

omit [Fintype V] in
theorem firstIn_eq_some_mem {order : List V} {I : Finset V} {v : V}
    (h : firstIn order I = some v) : v ∈ order ∧ v ∈ I := by
  sorry

omit [Fintype V] in
theorem beforeVertex_not_mem_of_firstIn_eq_some
    {order : List V} {I : Finset V} {v w : V}
    (h : firstIn order I = some v) (hw : w ∈ beforeVertex order v) :
    w ∉ I := by
  sorry

omit [Fintype V] in
theorem exists_eq_beforeVertex_append_of_firstIn_eq_some
    {order : List V} {I : Finset V} {v : V}
    (h : firstIn order I = some v) :
    ∃ after : List V, order = beforeVertex order v ++ v :: after := by
  sorry

/-- The next selected vertex, if the active set still meets the target. -/
noncomputable def nextVertex (I active : Finset V) : Option V :=
  firstIn (maxDegreeOrder G active) I

/-- Vertices removed from the active set when `v` is selected. -/
noncomputable def discarded (active : Finset V) (v : V) : Finset V :=
  insert v ((beforeVertex (maxDegreeOrder G active) v).toFinset ∪ G.neighborFinset v)

/-- One step of the graph-container algorithm.  If no active target vertex remains, the state is
left unchanged. -/
noncomputable def step (I : Finset V) (state : State V) : State V :=
  match nextVertex G I state.active with
  | none => state
  | some v =>
      { selected := insert v state.selected
        active := state.active \ discarded G state.active v }

/-- Run the graph-container algorithm for a prescribed number of steps. -/
noncomputable def run (I : Finset V) : ℕ → State V
  | 0 => State.initial
  | k + 1 => step G I (run I k)

/-- The selected fingerprint after `q` steps. -/
noncomputable def fingerprint (q : ℕ) (I : Finset V) : Finset V :=
  (run G I q).selected

/-- The active set after `q` steps. -/
noncomputable def activeAfter (q : ℕ) (I : Finset V) : Finset V :=
  (run G I q).active

@[simp]
theorem run_zero (I : Finset V) : run G I 0 = State.initial := by
  sorry

@[simp]
theorem run_succ (I : Finset V) (k : ℕ) :
    run G I (k + 1) = step G I (run G I k) := by
  sorry

theorem step_selected_mono (I : Finset V) (state : State V) :
    state.selected ⊆ (step G I state).selected := by
  sorry

theorem step_active_subset (I : Finset V) (state : State V) :
    (step G I state).active ⊆ state.active := by
  sorry

theorem run_selected_mono (I : Finset V) {j k : ℕ} (hjk : j ≤ k) :
    (run G I j).selected ⊆ (run G I k).selected := by
  sorry

theorem run_active_antitone (I : Finset V) {j k : ℕ} (hjk : j ≤ k) :
    (run G I k).active ⊆ (run G I j).active := by
  sorry

theorem fingerprint_subset (I : Finset V) (q : ℕ) :
    fingerprint G q I ⊆ I := by
  sorry

theorem fingerprint_isIndepSet {I : Finset V} (hI : G.IsIndepSet I) (q : ℕ) :
    G.IsIndepSet (fingerprint G q I) := by
  sorry

theorem selected_disjoint_active (I : Finset V) (q : ℕ) :
    Disjoint (fingerprint G q I) (activeAfter G q I) := by
  sorry

/-- Independent target vertices that have not been selected remain active. -/
theorem sdiff_fingerprint_subset_activeAfter {I : Finset V}
    (hI : G.IsIndepSet I) (q : ℕ) :
    I \ fingerprint G q I ⊆ activeAfter G q I := by
  sorry

theorem card_fingerprint_le (I : Finset V) (q : ℕ) :
    #(fingerprint G q I) ≤ q := by
  sorry

/-- If the target contains at least `q` vertices, all `q` iterations make progress. -/
theorem card_fingerprint_of_le_card {I : Finset V} (hI : G.IsIndepSet I)
    {q : ℕ} (hq : q ≤ #I) :
    #(fingerprint G q I) = q := by
  sorry

/-- Before the requested number of successful iterations has been reached, an active target
vertex is available. -/
theorem nextVertex_run_ne_none {I : Finset V} (hI : G.IsIndepSet I)
    {q k : ℕ} (hq : q ≤ #I) (hk : k < q) :
    nextVertex G I (run G I k).active ≠ none := by
  sorry

/-- The target is recovered from its fingerprint and residual set. -/
theorem fingerprint_union_sdiff (I : Finset V) (q : ℕ) :
    fingerprint G q I ∪ (I \ fingerprint G q I) = I := by
  sorry

/-- Reconstruction lemma: after `q` successful iterations, replaying the algorithm using only the
fingerprint produces the same state. -/
theorem run_fingerprint_eq_run {I : Finset V} (hI : G.IsIndepSet I)
    {q : ℕ} (hq : q ≤ #I) :
    run G (fingerprint G q I) q = run G I q := by
  sorry

end SimpleGraph.Container
