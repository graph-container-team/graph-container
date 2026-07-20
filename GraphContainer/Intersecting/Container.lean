/-
Copyright (c) 2026 Graph Container formalization team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Graph Container formalization team
-/
module

public import GraphContainer.Family
public import GraphContainer.Intersecting.Supersaturation
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Applying the graph-container theorem

Proposition 2.7 is converted into `Container.IsLocallyDense`, after which the general graph
container theorem gives the finite upper bound used in the asymptotic argument.
-/

@[expose] public section

open Finset

namespace SimpleGraph.KneserCounting

/-- The rounded container threshold corresponding to `(1 + ε) * starSize n k`. -/
noncomputable def containerThreshold (ε : ℝ) (n k : ℕ) : ℕ :=
  ⌈(1 + ε) * (starSize n k : ℝ)⌉₊

/-- The rounded fingerprint size used in the graph-container theorem. -/
noncomputable def fingerprintSize (ε : ℝ) (n k : ℕ) : ℕ :=
  ⌈(densityParameter ε n k)⁻¹ *
      Real.log ((vertexCount n k : ℝ) / (containerThreshold ε n k : ℝ))⌉₊

/-- Proposition 2.7 supplies precisely the local-density hypothesis required by the container
theorem. -/
theorem kneser_isLocallyDense
    {ε : ℝ} {n k : ℕ}
    (hε : 0 < ε)
    (hk : 0 < k)
    (hnk : 2 * k + 1 ≤ n) :
    Container.IsLocallyDense
      (graph n k)
      (densityParameter ε n k)
      (containerThreshold ε n k) := by
  intro S hS
  have hthreshold :
      (1 + ε) * (starSize n k : ℝ) ≤ (S.card : ℝ) := by
    apply Nat.ceil_le.mp
    simpa [containerThreshold] using hS
  exact kneser_supersaturation hε hk hnk S hthreshold

/-- The rounded parameters satisfy all hypotheses of the graph-container theorem.

The explicit `fingerprintSize ≤ vertexCount` assumption records the small correction missing from
the informal statement of the container theorem.
-/
theorem kneser_containerHypotheses
    {ε : ℝ} {n k : ℕ}
    (hε : 0 < ε) (hk : 0 < k) (hnk : 2 * k + 1 ≤ n)
    (hq : fingerprintSize ε n k ≤ vertexCount n k) :
    Container.Hypotheses (graph n k)
      (densityParameter ε n k)
      (containerThreshold ε n k)
      (fingerprintSize ε n k) := by
  refine
    { beta_pos := ?_
      beta_lt_one := ?_
      q_le_card := ?_
      locallyDense := kneser_isLocallyDense hε hk hnk
      shrink := ?_ }
  · unfold densityParameter regularDegree vertexCount
    have hk_nk : k ≤ n - k := by omega
    have hk_n : k ≤ n := by omega
    have hn_pos : 0 < n := by omega
    have hn_k_pos : 0 < n - k := by omega
    have hreg : 0 < (n - k).choose k := Nat.choose_pos hk_nk
    have hvertex : 0 < n.choose k := Nat.choose_pos hk_n
    positivity
  · have hk_nk : k ≤ n - k := by omega
    have hk_n : k ≤ n := by omega
    have hn_pos : 0 < n := by omega
    have hn_k_pos : 0 < n - k := by omega
    have hchoose : (n - k).choose k ≤ (n - 1).choose k := by
      exact Nat.choose_le_choose k (by omega)
    have hidentity : (n - 1).choose k * n = n.choose k * (n - k) := by
      simpa only [Nat.sub_add_cancel (by omega : 1 ≤ n)] using
        Nat.choose_mul_succ_eq (n - 1) k
    have hproduct : (n - k).choose k * n ≤ n.choose k * (n - k) := by
      rw [← hidentity]
      exact Nat.mul_le_mul_right n hchoose
    have hratio :
        ((regularDegree n k : ℝ) * (n : ℝ)) /
            ((vertexCount n k : ℝ) * ((n - k : ℕ) : ℝ)) ≤ 1 := by
      apply (div_le_one ?_).2
      · exact_mod_cast hproduct
      · unfold vertexCount
        have hvertex : 0 < n.choose k := Nat.choose_pos hk_n
        positivity
    have heps : ε / (1 + ε) < 1 := by
      apply (div_lt_one (by linarith)).2
      linarith
    have hratio_pos : 0 <
        ((regularDegree n k : ℝ) * (n : ℝ)) /
          ((vertexCount n k : ℝ) * ((n - k : ℕ) : ℝ)) := by
      unfold regularDegree vertexCount
      have hreg : 0 < (n - k).choose k := Nat.choose_pos hk_nk
      have hvertex : 0 < n.choose k := Nat.choose_pos hk_n
      positivity
    unfold densityParameter
    nlinarith [div_pos hε (by linarith : 0 < 1 + ε)]
  · simpa only [card_vertex] using hq
  · have hβ : 0 < densityParameter ε n k := by
      unfold densityParameter regularDegree vertexCount
      have hk_nk : k ≤ n - k := by omega
      have hk_n : k ≤ n := by omega
      have hn_pos : 0 < n := by omega
      have hn_k_pos : 0 < n - k := by omega
      have hreg : 0 < (n - k).choose k := Nat.choose_pos hk_nk
      have hvertex : 0 < n.choose k := Nat.choose_pos hk_n
      positivity
    have hstar : 0 < starSize n k := by
      unfold starSize
      exact Nat.choose_pos (by omega)
    have hV : 0 < (vertexCount n k : ℝ) := by
      unfold vertexCount
      have hvertex : 0 < n.choose k := Nat.choose_pos (by omega)
      positivity
    have hR : 0 < (containerThreshold ε n k : ℝ) := by
      have hbase : 0 < (1 + ε) * (starSize n k : ℝ) := by positivity
      have hceil := Nat.le_ceil ((1 + ε) * (starSize n k : ℝ))
      rw [← containerThreshold] at hceil
      linarith
    have hq_lower :
        (densityParameter ε n k)⁻¹ *
            Real.log ((vertexCount n k : ℝ) / (containerThreshold ε n k : ℝ)) ≤
          (fingerprintSize ε n k : ℝ) := by
      exact Nat.le_ceil _
    have hlog :
        Real.log ((vertexCount n k : ℝ) / (containerThreshold ε n k : ℝ)) ≤
          densityParameter ε n k * (fingerprintSize ε n k : ℝ) := by
      calc
        Real.log ((vertexCount n k : ℝ) / (containerThreshold ε n k : ℝ)) =
            densityParameter ε n k *
              ((densityParameter ε n k)⁻¹ *
                Real.log ((vertexCount n k : ℝ) /
                  (containerThreshold ε n k : ℝ))) := by
              field_simp
        _ ≤ densityParameter ε n k * (fingerprintSize ε n k : ℝ) :=
          mul_le_mul_of_nonneg_left hq_lower hβ.le
    have hexp :
        Real.exp (-(densityParameter ε n k) * (fingerprintSize ε n k : ℝ)) ≤
          Real.exp (-Real.log ((vertexCount n k : ℝ) /
            (containerThreshold ε n k : ℝ))) := by
      apply Real.exp_le_exp.mpr
      linarith
    calc
      Real.exp (-(densityParameter ε n k) * (fingerprintSize ε n k : ℝ)) *
            (Fintype.card (Vertex n k) : ℝ) =
          Real.exp (-(densityParameter ε n k) * (fingerprintSize ε n k : ℝ)) *
            (vertexCount n k : ℝ) := by rw [card_vertex]
      _ ≤ Real.exp (-Real.log ((vertexCount n k : ℝ) /
            (containerThreshold ε n k : ℝ))) * (vertexCount n k : ℝ) :=
        mul_le_mul_of_nonneg_right hexp hV.le
      _ = (containerThreshold ε n k : ℝ) := by
        rw [Real.exp_neg, Real.exp_log (div_pos hV hR)]
        field_simp

/-- The finite upper bound obtained from any valid set of Kneser-container parameters. -/
theorem intersectingFamilyCount_le
    {β : ℝ} {n k R q : ℕ}
    (hk : 0 < k) (h : Container.Hypotheses (graph n k) β R q) :
    intersectingFamilyCount n k ≤
      (vertexCount n k).choose q * 2 ^ (R + q) := by
  classical
  obtain ⟨𝒞, h𝒞_card, h𝒞_size, h𝒞_cover⟩ :=
    Container.graph_container_theorem (G := graph n k) h
  have hcovered : intersectingFamilies n k ⊆ 𝒞.biUnion Finset.powerset := by
    intro I hI
    have hI_indep : (graph n k).IsIndepSet I :=
      (isIntersecting_iff_isIndepSet n k hk I).mp
        ((mem_intersectingFamilies (n := n) (k := k)).mp hI)
    obtain ⟨C, hC, hIC⟩ := h𝒞_cover I hI_indep
    exact Finset.mem_biUnion.mpr ⟨C, hC, Finset.mem_powerset.mpr hIC⟩
  unfold intersectingFamilyCount
  calc
    #(intersectingFamilies n k) ≤ #(𝒞.biUnion Finset.powerset) :=
      Finset.card_le_card hcovered
    _ ≤ #𝒞 * 2 ^ (R + q) := by
      apply Finset.card_biUnion_le_card_mul
      intro C hC
      rw [Finset.card_powerset]
      exact Nat.pow_le_pow_right (by decide) (h𝒞_size C hC)
    _ ≤ (Fintype.card (Vertex n k)).choose q * 2 ^ (R + q) :=
      Nat.mul_le_mul_right (2 ^ (R + q)) h𝒞_card
    _ = (vertexCount n k).choose q * 2 ^ (R + q) := by
      rw [card_vertex]

end SimpleGraph.KneserCounting
