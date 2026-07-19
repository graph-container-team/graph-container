/-
Copyright (c) 2026 Graph Container formalization team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Graph Container formalization team
-/
module

public import GraphContainer.Algorithm

import Mathlib.Data.Nat.Choose.Cast

/-!
# Density and shrinkage estimates

This file isolates the quantitative part of the graph-container proof.  Local edge density forces
a large maximum degree in the relevant suffix of the max-degree ordering.  Consequently the active
set shrinks by a factor of at most `1 - β` at each successful iteration, until it has size at most
`R`.

This is work package 3 in `IMPLEMENTATION.md`.
-/

@[expose] public section

open scoped BigOperators
open Finset

namespace SimpleGraph.Container

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Degree-sum formula restricted to a vertex finset. -/
theorem sum_degreeWithin_eq_twice_inducedEdgeCount (A : Finset V) :
    (∑ v ∈ A, degreeWithin G A v) = 2 * inducedEdgeCount G A := by
  classical
  rw [← Finset.sum_coe_sort A]
  simp_rw [degreeWithin_eq_degree_induce]
  exact (G.induce (A : Set V)).sum_degrees_eq_twice_card_edges

/-- The degree sum is at most the cardinality times the degree of any vertex whose degree is
maximal on the finset. -/
theorem twice_inducedEdgeCount_le_card_mul_degreeWithin_of_forall_le
    {A : Finset V} {v : V}
    (hmax : ∀ w ∈ A, degreeWithin G A w ≤ degreeWithin G A v) :
    2 * inducedEdgeCount G A ≤ #A * degreeWithin G A v := by
  have hsum :
      (∑ w ∈ A, degreeWithin G A w) ≤ #A * degreeWithin G A v := by
    simpa [nsmul_eq_mul] using
      A.sum_le_card_nsmul (degreeWithin G A) (degreeWithin G A v) hmax
  rwa [sum_degreeWithin_eq_twice_inducedEdgeCount] at hsum

/-- Some vertex has at least the average degree in a nonempty induced subgraph. -/
theorem exists_average_le_degreeWithin {A : Finset V} (hA : A.Nonempty) :
    ∃ v ∈ A,
      2 * inducedEdgeCount G A ≤ #A * degreeWithin G A v := by
  let v := maxDegreeVertex G A hA
  have hv := maxDegreeVertex_mem G A hA
  refine ⟨v, hv, ?_⟩
  exact
    twice_inducedEdgeCount_le_card_mul_degreeWithin_of_forall_le G
      (fun w hw ↦ degreeWithin_le_maxDegreeVertex G A hA w hw)

/-- Local density bounds the degree of any vertex whose degree is maximal on the finset. -/
theorem beta_mul_card_sub_one_le_degreeWithin_of_forall_le
    {β : ℝ} {R : ℕ} (hdense : IsLocallyDense G β R)
    {A : Finset V} {v : V} (hAR : R ≤ #A) (hv : v ∈ A)
    (hmax : ∀ w ∈ A, degreeWithin G A w ≤ degreeWithin G A v) :
    β * ((#A - 1 : ℕ) : ℝ) ≤ (degreeWithin G A v : ℝ) := by
  have havgNat :=
    twice_inducedEdgeCount_le_card_mul_degreeWithin_of_forall_le G hmax
  have havg :
      (2 : ℝ) * (inducedEdgeCount G A : ℝ) ≤
        (#A : ℝ) * (degreeWithin G A v : ℝ) := by
    exact_mod_cast havgNat
  have hd := hdense A hAR
  have hd2 := mul_le_mul_of_nonneg_left hd (show (0 : ℝ) ≤ 2 by norm_num)
  rw [Nat.cast_choose_two ℝ] at hd2
  have hA : A.Nonempty := ⟨v, hv⟩
  have hA1 : 1 ≤ #A := Finset.one_le_card.mpr hA
  have hApos : (0 : ℝ) < (#A : ℝ) := by exact_mod_cast (Finset.card_pos.mpr hA)
  rw [Nat.cast_sub hA1]
  norm_num at hd2 ⊢
  nlinarith

/-- Local density gives the selected maximum-degree vertex at least `β * (|A| - 1)` neighbors. -/
theorem beta_mul_card_sub_one_le_degreeWithin_maxDegreeVertex
    {β : ℝ} {R : ℕ} (hdense : IsLocallyDense G β R)
    {A : Finset V} (hAR : R ≤ #A) (hA : A.Nonempty) :
    β * ((#A - 1 : ℕ) : ℝ) ≤
      (degreeWithin G A (maxDegreeVertex G A hA) : ℝ) := by
  refine
    beta_mul_card_sub_one_le_degreeWithin_of_forall_le G hdense hAR
      (maxDegreeVertex_mem G A hA) ?_
  intro w hw
  exact degreeWithin_le_maxDegreeVertex G A hA w hw

/-- The discarded portion of a successful step contains at least a `β` fraction of the old active
set, provided the new active set is still larger than `R`. -/
theorem beta_mul_card_le_card_inter_discarded
    {β : ℝ} {R : ℕ} (hβ_one : β ≤ 1)
    (hdense : IsLocallyDense G β R) {I : Finset V} {state : State V} {v : V}
    (hnext : nextVertex G I state.active = some v)
    (hlarge : R < #(step G I state).active) :
    β * (#state.active : ℝ) ≤
      (#(state.active ∩ discarded G state.active v) : ℝ) := by
  have hfirst : firstIn (maxDegreeOrder G state.active) I = some v := by
    simpa [nextVertex] using hnext
  obtain ⟨after, horder⟩ :=
    exists_eq_beforeVertex_append_of_firstIn_eq_some hfirst
  let P : Finset V := (beforeVertex (maxDegreeOrder G state.active) v).toFinset
  let B : Finset V := (v :: after).toFinset
  let N : Finset V := G.neighborFinset v ∩ B
  have hnodup :
      (beforeVertex (maxDegreeOrder G state.active) v ++ v :: after).Nodup := by
    rw [← horder]
    exact maxDegreeOrder_nodup G state.active
  have hPB : Disjoint P B := by
    apply List.disjoint_toFinset_iff_disjoint.mpr
    exact (List.nodup_append'.mp hnodup).2.2
  have hactive : state.active = P ∪ B := by
    have h := congrArg List.toFinset horder
    simpa [P, B] using h
  have hvB : v ∈ B := by simp [B]
  have hB : B.Nonempty := ⟨v, hvB⟩
  have hstep :
      (step G I state).active = state.active \ discarded G state.active v := by
    simp [step, hnext]
  have hstepB : (step G I state).active ⊆ B := by
    rw [hstep]
    intro x hx
    rcases Finset.mem_sdiff.mp hx with ⟨hxactive, hxdiscarded⟩
    rw [hactive] at hxactive
    rcases Finset.mem_union.mp hxactive with hxP | hxB
    · exfalso
      apply hxdiscarded
      simp [discarded, P, hxP]
    · exact hxB
  have hRB : R ≤ #B :=
    Nat.le_of_lt (hlarge.trans_le (Finset.card_le_card hstepB))
  have hbetaB :
      β * ((#B - 1 : ℕ) : ℝ) ≤ (degreeWithin G B v : ℝ) := by
    refine
      (beta_mul_card_sub_one_le_degreeWithin_maxDegreeVertex G hdense hRB hB).trans ?_
    exact_mod_cast
      degreeWithin_le_of_maxDegreeOrder_eq_append_cons G state.active horder
        (maxDegreeVertex_mem G B hB)
  have hPN : Disjoint P N := by
    rw [Finset.disjoint_left]
    intro x hxP hxN
    exact (Finset.disjoint_left.mp hPB hxP (Finset.mem_inter.mp hxN).2)
  have hvP : v ∉ P := by
    intro hv
    exact Finset.disjoint_left.mp hPB hv hvB
  have hvN : v ∉ N := by
    simp [N]
  have hvPUN : v ∉ P ∪ N := by simp [hvP, hvN]
  have hcardSmall :
      #(insert v (P ∪ N)) = #P + #N + 1 := by
    rw [Finset.card_insert_of_notMem hvPUN, Finset.card_union_of_disjoint hPN]
  have hsmall :
      insert v (P ∪ N) ⊆ state.active ∩ discarded G state.active v := by
    intro x hx
    rw [Finset.mem_inter]
    rcases Finset.mem_insert.mp hx with rfl | hx
    · constructor
      · rw [hactive]
        exact Finset.mem_union_right P hvB
      · simp [discarded]
    · rcases Finset.mem_union.mp hx with hxP | hxN
      · constructor
        · rw [hactive]
          exact Finset.mem_union_left B hxP
        · simp [discarded, P, hxP]
      · have hxNB := Finset.mem_inter.mp hxN
        constructor
        · rw [hactive]
          exact Finset.mem_union_right P hxNB.2
        · rw [discarded, Finset.mem_insert, Finset.mem_union]
          exact Or.inr (Or.inr hxNB.1)
  have hcardActive : #state.active = #P + #B := by
    rw [hactive, Finset.card_union_of_disjoint hPB]
  have hB1 : 1 ≤ #B := Finset.one_le_card.mpr hB
  have hcardBcast : ((#B : ℕ) : ℝ) = ((#B - 1 : ℕ) : ℝ) + 1 := by
    norm_num [Nat.cast_sub hB1]
  have hbetaSmall :
      β * (#state.active : ℝ) ≤ (#(insert v (P ∪ N)) : ℝ) := by
    rw [hcardActive, hcardSmall]
    simp only [Nat.cast_add, Nat.cast_one]
    change
      β * ((#P : ℝ) + (#B : ℝ)) ≤
        (#P : ℝ) + (#N : ℝ) + 1
    change β * ((#B - 1 : ℕ) : ℝ) ≤ (#N : ℝ) at hbetaB
    rw [hcardBcast]
    have hPnonneg : (0 : ℝ) ≤ (#P : ℝ) := Nat.cast_nonneg #P
    nlinarith
  exact hbetaSmall.trans (by exact_mod_cast Finset.card_le_card hsmall)

/-- One successful iteration contracts the active set by a factor of at most `1 - β`. -/
theorem card_step_active_le_one_sub_mul
    {β : ℝ} {R : ℕ} (hβ_one : β ≤ 1)
    (hdense : IsLocallyDense G β R) {I : Finset V} {state : State V}
    (hprogress : nextVertex G I state.active ≠ none)
    (hlarge : R < #(step G I state).active) :
    (#(step G I state).active : ℝ) ≤ (1 - β) * (#state.active : ℝ) := by
  cases hnext : nextVertex G I state.active with
  | none => exact (hprogress hnext).elim
  | some v =>
      have hdeleted :=
        beta_mul_card_le_card_inter_discarded G hβ_one hdense hnext hlarge
      have hstep :
          (step G I state).active =
            state.active \ discarded G state.active v := by
        simp [step, hnext]
      have hcard :=
        Finset.card_inter_add_card_sdiff state.active (discarded G state.active v)
      have hcardR :
          (#(state.active ∩ discarded G state.active v) : ℝ) +
              (#(state.active \ discarded G state.active v) : ℝ) =
            (#state.active : ℝ) := by
        exact_mod_cast hcard
      rw [hstep]
      nlinarith

/-- A successful step has either reached the threshold or contracts the active set by a factor of
at most `1 - β`. -/
theorem card_step_active_le_threshold_or_le_one_sub_mul
    {β : ℝ} {R : ℕ} (hβ_one : β ≤ 1)
    (hdense : IsLocallyDense G β R) {I : Finset V} {state : State V}
    (hprogress : nextVertex G I state.active ≠ none) :
    #(step G I state).active ≤ R ∨
      (#(step G I state).active : ℝ) ≤ (1 - β) * (#state.active : ℝ) := by
  by_cases hlarge : R < #(step G I state).active
  · exact Or.inr <| card_step_active_le_one_sub_mul G hβ_one hdense hprogress hlarge
  · exact Or.inl (Nat.le_of_not_gt hlarge)

/-- Conditional geometric decay after `q` iterations.  Assuming the final active set is larger
than `R` ensures that local density was available at every earlier iteration. -/
theorem card_activeAfter_le_pow_mul_card
    {β : ℝ} {R q : ℕ} (hβ_one : β ≤ 1)
    (hdense : IsLocallyDense G β R) {I : Finset V}
    (hI : G.IsIndepSet I) (hqI : q ≤ #I)
    (hlarge : R < #(activeAfter G q I)) :
    (#(activeAfter G q I) : ℝ) ≤
      (1 - β) ^ q * (Fintype.card V : ℝ) := by
  induction q with
  | zero =>
      simp [activeAfter, run, State.initial]
  | succ q ih =>
      have hqI' : q ≤ #I := (Nat.le_succ q).trans hqI
      have hsubset :
          activeAfter G (q + 1) I ⊆ activeAfter G q I := by
        exact run_active_antitone G I (Nat.le_succ q)
      have hlarge' : R < #(activeAfter G q I) :=
        hlarge.trans_le (Finset.card_le_card hsubset)
      have hprogress :
          nextVertex G I (run G I q).active ≠ none :=
        nextVertex_run_ne_none G hI hqI (Nat.lt_succ_self q)
      have hcontract :
          (#(activeAfter G (q + 1) I) : ℝ) ≤
            (1 - β) * (#(activeAfter G q I) : ℝ) := by
        simpa [activeAfter, run_succ] using
          card_step_active_le_one_sub_mul G hβ_one hdense hprogress hlarge
      calc
        (#(activeAfter G (q + 1) I) : ℝ) ≤
            (1 - β) * (#(activeAfter G q I) : ℝ) := hcontract
        _ ≤ (1 - β) * ((1 - β) ^ q * (Fintype.card V : ℝ)) :=
          mul_le_mul_of_nonneg_left (ih hqI' hlarge') (sub_nonneg.mpr hβ_one)
        _ = (1 - β) ^ (q + 1) * (Fintype.card V : ℝ) := by
          rw [pow_succ]
          ring

/-- After `q` iterations, the active set has either reached the threshold or satisfies the
geometric decay bound. -/
theorem card_activeAfter_le_threshold_or_le_pow_mul_card
    {β : ℝ} {R q : ℕ} (hβ_one : β ≤ 1)
    (hdense : IsLocallyDense G β R) {I : Finset V}
    (hI : G.IsIndepSet I) (hqI : q ≤ #I) :
    #(activeAfter G q I) ≤ R ∨
      (#(activeAfter G q I) : ℝ) ≤
        (1 - β) ^ q * (Fintype.card V : ℝ) := by
  by_cases hlarge : R < #(activeAfter G q I)
  · exact Or.inr <| card_activeAfter_le_pow_mul_card G hβ_one hdense hI hqI hlarge
  · exact Or.inl (Nat.le_of_not_gt hlarge)

/-- The elementary analytic estimate used by the paper. -/
theorem one_sub_pow_le_exp_neg_mul {β : ℝ} (hβ_one : β ≤ 1) (q : ℕ) :
    (1 - β) ^ q ≤ Real.exp (-β * (q : ℝ)) := by
  calc
    (1 - β) ^ q ≤ Real.exp (-β) ^ q :=
      pow_le_pow_left₀ (sub_nonneg.mpr hβ_one) (Real.one_sub_le_exp_neg β) q
    _ = Real.exp (-β * (q : ℝ)) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring

/-- The final active set for an independent target of size at least `q` has at most `R` vertices. -/
theorem card_activeAfter_le {β : ℝ} {R q : ℕ} (h : Hypotheses G β R q)
    {I : Finset V} (hI : G.IsIndepSet I) (hqI : q ≤ #I) :
    #(activeAfter G q I) ≤ R := by
  rcases
      card_activeAfter_le_threshold_or_le_pow_mul_card G h.beta_lt_one.le
        h.locallyDense hI hqI with hsmall | hpow
  · exact hsmall
  · have hexp := one_sub_pow_le_exp_neg_mul h.beta_lt_one.le q
    have hcard_nonneg : (0 : ℝ) ≤ (Fintype.card V : ℝ) := Nat.cast_nonneg _
    have hreal :
        (#(activeAfter G q I) : ℝ) ≤
          Real.exp (-β * (q : ℝ)) * (Fintype.card V : ℝ) :=
      hpow.trans (mul_le_mul_of_nonneg_right hexp hcard_nonneg)
    exact_mod_cast hreal.trans h.shrink

end SimpleGraph.Container
