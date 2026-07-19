/-
Copyright (c) 2026 Graph Container formalization team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Graph Container formalization team
-/
module

public import GraphContainer.Basic
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
  change order.find? (fun x ↦ decide (x ∈ I)) = some v at h
  constructor
  · exact List.mem_of_find?_eq_some h
  · have hv : decide (v ∈ I) = true :=
      List.find?_some (p := fun x ↦ decide (x ∈ I)) h
    exact of_decide_eq_true hv

omit [Fintype V] in
theorem beforeVertex_not_mem_of_firstIn_eq_some
    {order : List V} {I : Finset V} {v w : V}
    (h : firstIn order I = some v) (hw : w ∈ beforeVertex order v) :
    w ∉ I := by
  induction order with
  | nil => simp [beforeVertex] at hw
  | cons a order ih =>
      by_cases haI : a ∈ I
      · have hav : a = v := by
          simpa [firstIn, haI] using h
        subst a
        simp [beforeVertex] at hw
      · have htail : firstIn order I = some v := by
          simpa [firstIn, haI] using h
        by_cases hav : a = v
        · subst a
          simp [beforeVertex] at hw
        · simp only [beforeVertex, List.takeWhile_cons] at hw
          rw [if_pos (by simp [hav])] at hw
          simp only [List.mem_cons] at hw
          rcases hw with rfl | hw
          · exact haI
          · exact ih htail hw

omit [Fintype V] in
theorem exists_eq_beforeVertex_append_of_firstIn_eq_some
    {order : List V} {I : Finset V} {v : V}
    (h : firstIn order I = some v) :
    ∃ after : List V, order = beforeVertex order v ++ v :: after := by
  induction order with
  | nil => simp [firstIn] at h
  | cons a order ih =>
      by_cases haI : a ∈ I
      · have hav : a = v := by
          simpa [firstIn, haI] using h
        subst a
        exact ⟨order, by simp [beforeVertex]⟩
      · have htail : firstIn order I = some v := by
          simpa [firstIn, haI] using h
        obtain ⟨after, horder⟩ := ih htail
        have hav : a ≠ v := by
          intro hav
          subst a
          exact haI (firstIn_eq_some_mem htail).2
        have hbefore : beforeVertex (a :: order) v = a :: beforeVertex order v := by
          simp only [beforeVertex, List.takeWhile_cons]
          rw [if_pos (by simp [hav])]
        refine ⟨after, ?_⟩
        calc
          a :: order = a :: (beforeVertex order v ++ v :: after) :=
            congrArg (a :: ·) horder
          _ = (a :: beforeVertex order v) ++ v :: after := rfl
          _ = beforeVertex (a :: order) v ++ v :: after := by rw [hbefore]

omit [Fintype V] in
private theorem firstIn_eq_some_of_subset
    {order : List V} {I J : Finset V} {v : V}
    (hJI : J ⊆ I) (hvJ : v ∈ J) (h : firstIn order I = some v) :
    firstIn order J = some v := by
  obtain ⟨after, horder⟩ := exists_eq_beforeVertex_append_of_firstIn_eq_some h
  change order.find? (fun x ↦ decide (x ∈ J)) = some v
  refine List.find?_eq_some_iff_append.mpr ⟨by simp [hvJ], ?_⟩
  refine ⟨beforeVertex order v, after, horder, ?_⟩
  intro w hw
  have hwI : w ∉ I := beforeVertex_not_mem_of_firstIn_eq_some h hw
  have hwJ : w ∉ J := fun hwJ ↦ hwI (hJI hwJ)
  simp [hwJ]

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
  rfl

@[simp]
theorem run_succ (I : Finset V) (k : ℕ) :
    run G I (k + 1) = step G I (run G I k) := by
  rfl

theorem step_selected_mono (I : Finset V) (state : State V) :
    state.selected ⊆ (step G I state).selected := by
  cases hnext : nextVertex G I state.active with
  | none => simp [step, hnext]
  | some v => simp [step, hnext]

theorem step_active_subset (I : Finset V) (state : State V) :
    (step G I state).active ⊆ state.active := by
  cases hnext : nextVertex G I state.active with
  | none => simp [step, hnext]
  | some v => simp [step, hnext]

theorem run_selected_mono (I : Finset V) {j k : ℕ} (hjk : j ≤ k) :
    (run G I j).selected ⊆ (run G I k).selected := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hjk
  clear hjk
  induction d with
  | zero => exact Subset.rfl
  | succ d ih =>
      apply ih.trans
      rw [show j + Nat.succ d = (j + d) + 1 by omega, run_succ]
      exact step_selected_mono G I (run G I (j + d))

theorem run_active_antitone (I : Finset V) {j k : ℕ} (hjk : j ≤ k) :
    (run G I k).active ⊆ (run G I j).active := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hjk
  clear hjk
  induction d with
  | zero => exact Subset.rfl
  | succ d ih =>
      rw [show j + Nat.succ d = (j + d) + 1 by omega, run_succ]
      exact (step_active_subset G I (run G I (j + d))).trans ih

theorem fingerprint_subset (I : Finset V) (q : ℕ) :
    fingerprint G q I ⊆ I := by
  induction q with
  | zero => simp [fingerprint, State.initial]
  | succ q ih =>
      cases hnext : nextVertex G I (run G I q).active with
      | none => simpa [fingerprint, step, hnext] using ih
      | some v =>
          have hvI : v ∈ I := by
            exact (firstIn_eq_some_mem (by simpa [nextVertex] using hnext)).2
          intro x hx
          have hx' : x = v ∨ x ∈ fingerprint G q I := by
            simpa [fingerprint, step, hnext] using hx
          rcases hx' with rfl | hx'
          · exact hvI
          · exact ih hx'

theorem fingerprint_isIndepSet {I : Finset V} (hI : G.IsIndepSet I) (q : ℕ) :
    G.IsIndepSet (fingerprint G q I) := by
  rw [SimpleGraph.isIndepSet_iff] at hI ⊢
  exact Set.Pairwise.mono (by simpa using fingerprint_subset G I q) hI

theorem selected_disjoint_active (I : Finset V) (q : ℕ) :
    Disjoint (fingerprint G q I) (activeAfter G q I) := by
  induction q with
  | zero => simp [fingerprint, activeAfter, State.initial]
  | succ q ih =>
      cases hnext : nextVertex G I (run G I q).active with
      | none => simpa [fingerprint, activeAfter, step, hnext] using ih
      | some v =>
          rw [Finset.disjoint_left]
          intro x hxselected hxactive
          have hxselected' : x = v ∨ x ∈ fingerprint G q I := by
            simpa [fingerprint, step, hnext] using hxselected
          have hxactive' :
              x ∈ activeAfter G q I ∧
                x ∉ discarded G (run G I q).active v := by
            simpa [activeAfter, step, hnext] using hxactive
          rcases hxselected' with rfl | hxselected'
          · exact hxactive'.2 (by simp [discarded])
          · exact Finset.disjoint_left.mp ih hxselected' hxactive'.1

/-- Independent target vertices that have not been selected remain active. -/
theorem sdiff_fingerprint_subset_activeAfter {I : Finset V}
    (hI : G.IsIndepSet I) (q : ℕ) :
    I \ fingerprint G q I ⊆ activeAfter G q I := by
  induction q with
  | zero => simp [fingerprint, activeAfter, State.initial]
  | succ q ih =>
      cases hnext : nextVertex G I (run G I q).active with
      | none => simpa [fingerprint, activeAfter, step, hnext] using ih
      | some v =>
          have hfirst : firstIn (maxDegreeOrder G (run G I q).active) I = some v := by
            simpa [nextVertex] using hnext
          have hvI : v ∈ I := (firstIn_eq_some_mem hfirst).2
          intro x hx
          have hxI : x ∈ I := (Finset.mem_sdiff.mp hx).1
          have hxnotSelected : x ∉ fingerprint G (q + 1) I :=
            (Finset.mem_sdiff.mp hx).2
          have hxnotv : x ≠ v := by
            intro hxv
            subst x
            apply hxnotSelected
            simp [fingerprint, step, hnext]
          have hxnotOld : x ∉ fingerprint G q I := by
            intro hxOld
            exact hxnotSelected (run_selected_mono G I (Nat.le_succ q) hxOld)
          have hxactive : x ∈ activeAfter G q I :=
            ih (Finset.mem_sdiff.mpr ⟨hxI, hxnotOld⟩)
          have hxdiscarded : x ∉ discarded G (run G I q).active v := by
            intro hxdiscarded
            rcases Finset.mem_insert.mp hxdiscarded with hxv | hxdiscarded
            · exact hxnotv hxv
            · rcases Finset.mem_union.mp hxdiscarded with hxprefix | hxneighbor
              · exact
                  (beforeVertex_not_mem_of_firstIn_eq_some hfirst
                    (List.mem_toFinset.mp hxprefix)) hxI
              · have hadj : G.Adj v x := (G.mem_neighborFinset v x).mp hxneighbor
                have hpair := (SimpleGraph.isIndepSet_iff G).mp hI
                exact (hpair hvI hxI (Ne.symm hxnotv)) hadj
          have hxnew :
              x ∈ (run G I q).active \ discarded G (run G I q).active v :=
            Finset.mem_sdiff.mpr ⟨by simpa [activeAfter] using hxactive, hxdiscarded⟩
          simpa [activeAfter, step, hnext] using hxnew

theorem card_fingerprint_le (I : Finset V) (q : ℕ) :
    #(fingerprint G q I) ≤ q := by
  induction q with
  | zero => simp [fingerprint, State.initial]
  | succ q ih =>
      cases hnext : nextVertex G I (run G I q).active with
      | none =>
          simpa [fingerprint, step, hnext] using ih.trans (Nat.le_succ q)
      | some v =>
          calc
            #(fingerprint G (q + 1) I) = #(insert v (fingerprint G q I)) := by
              simp [fingerprint, step, hnext]
            _ ≤ #(fingerprint G q I) + 1 := Finset.card_insert_le v _
            _ ≤ q + 1 := Nat.add_le_add_right ih 1

private theorem nextVertex_run_ne_none_of_card_fingerprint_lt
    {I : Finset V} (hI : G.IsIndepSet I) {k : ℕ}
    (hlt : #(fingerprint G k I) < #I) :
    nextVertex G I (run G I k).active ≠ none := by
  have hnotSubset : ¬I ⊆ fingerprint G k I := by
    intro hsubset
    exact (Nat.not_lt_of_ge (Finset.card_le_card hsubset)) hlt
  obtain ⟨x, hxI, hxnotSelected⟩ := Finset.not_subset.mp hnotSubset
  have hxactive : x ∈ activeAfter G k I :=
    sdiff_fingerprint_subset_activeAfter G hI k
      (Finset.mem_sdiff.mpr ⟨hxI, hxnotSelected⟩)
  have hxorder : x ∈ maxDegreeOrder G (run G I k).active := by
    apply List.mem_toFinset.mp
    simpa [activeAfter] using hxactive
  intro hnone
  have hfind :
      (maxDegreeOrder G (run G I k).active).find?
          (fun y ↦ decide (y ∈ I)) = none := by
    simpa [nextVertex, firstIn] using hnone
  have hxfalse := List.find?_eq_none.mp hfind x hxorder
  simp [hxI] at hxfalse

/-- If the target contains at least `q` vertices, all `q` iterations make progress. -/
theorem card_fingerprint_of_le_card {I : Finset V} (hI : G.IsIndepSet I)
    {q : ℕ} (hq : q ≤ #I) :
    #(fingerprint G q I) = q := by
  induction q with
  | zero => simp [fingerprint, State.initial]
  | succ q ih =>
      have hqI : q ≤ #I := (Nat.le_succ q).trans hq
      have ihcard : #(fingerprint G q I) = q := ih hqI
      have hlt : #(fingerprint G q I) < #I := by omega
      have hprogress :=
        nextVertex_run_ne_none_of_card_fingerprint_lt G hI hlt
      cases hnext : nextVertex G I (run G I q).active with
      | none => exact (hprogress hnext).elim
      | some v =>
          have hfirst :
              firstIn (maxDegreeOrder G (run G I q).active) I = some v := by
            simpa [nextVertex] using hnext
          have hvactive : v ∈ activeAfter G q I := by
            have hvorder := (firstIn_eq_some_mem hfirst).1
            have hvfinset :
                v ∈ (maxDegreeOrder G (run G I q).active).toFinset :=
              List.mem_toFinset.mpr hvorder
            simpa [activeAfter] using hvfinset
          have hvnotSelected : v ∉ fingerprint G q I := by
            intro hvselected
            exact
              Finset.disjoint_left.mp (selected_disjoint_active G I q)
                hvselected hvactive
          calc
            #(fingerprint G (q + 1) I) = #(insert v (fingerprint G q I)) := by
              simp [fingerprint, step, hnext]
            _ = #(fingerprint G q I) + 1 :=
              Finset.card_insert_of_notMem hvnotSelected
            _ = q + 1 := by rw [ihcard]

/-- Before the requested number of successful iterations has been reached, an active target
vertex is available. -/
theorem nextVertex_run_ne_none {I : Finset V} (hI : G.IsIndepSet I)
    {q k : ℕ} (hq : q ≤ #I) (hk : k < q) :
    nextVertex G I (run G I k).active ≠ none := by
  apply nextVertex_run_ne_none_of_card_fingerprint_lt G hI
  rw [card_fingerprint_of_le_card G hI (Nat.le_of_lt hk |>.trans hq)]
  exact hk.trans_le hq

/-- The target is recovered from its fingerprint and residual set. -/
theorem fingerprint_union_sdiff (I : Finset V) (q : ℕ) :
    fingerprint G q I ∪ (I \ fingerprint G q I) = I := by
  exact Finset.union_sdiff_of_subset (fingerprint_subset G I q)

/-- Reconstruction lemma: after `q` successful iterations, replaying the algorithm using only the
fingerprint produces the same state. -/
theorem run_fingerprint_eq_run {I : Finset V} (hI : G.IsIndepSet I)
    {q : ℕ} (hq : q ≤ #I) :
    run G (fingerprint G q I) q = run G I q := by
  let S := fingerprint G q I
  have hSI : S ⊆ I := by
    simpa [S] using fingerprint_subset G I q
  have hreplay : ∀ k, k ≤ q → run G S k = run G I k := by
    intro k
    induction k with
    | zero =>
        intro _
        simp
    | succ k ih =>
        intro hk
        have hk' : k ≤ q := (Nat.le_succ k).trans hk
        have hrunk : run G S k = run G I k := ih hk'
        have hklt : k < q := Nat.lt_of_succ_le hk
        have hprogress : nextVertex G I (run G I k).active ≠ none :=
          nextVertex_run_ne_none G hI hq hklt
        cases hnext : nextVertex G I (run G I k).active with
        | none => exact (hprogress hnext).elim
        | some v =>
            have hfirst :
                firstIn (maxDegreeOrder G (run G I k).active) I = some v := by
              simpa [nextVertex] using hnext
            have hvNext : v ∈ (run G I (k + 1)).selected := by
              simp [step, hnext]
            have hvS : v ∈ S := by
              simpa [S, fingerprint] using run_selected_mono G I hk hvNext
            have hfirstS :
                firstIn (maxDegreeOrder G (run G I k).active) S = some v :=
              firstIn_eq_some_of_subset hSI hvS hfirst
            have hnextS : nextVertex G S (run G I k).active = some v := by
              simpa [nextVertex] using hfirstS
            rw [run_succ, run_succ, hrunk]
            simp [step, hnextS, hnext]
  exact hreplay q (Nat.le_refl q)

end SimpleGraph.Container