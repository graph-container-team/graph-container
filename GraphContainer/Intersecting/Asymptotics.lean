/-
Copyright (c) 2026 Graph Container formalization team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Graph Container formalization team
-/
module

public import GraphContainer.Intersecting.Container
public import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Data.Nat.Choose.Bounds

/-!
# An entropy bound for counting intersecting families

This file turns the finite graph-container estimate into a power of two, proves that its two
explicit error hypotheses hold uniformly for all admissible `k` once `n` is sufficiently large,
and combines the result with the elementary full-star lower bound.
-/

@[expose] public section

namespace SimpleGraph.KneserCounting

open Filter Asymptotics

/-- # entropyCost ≥ log_2 binom{N}{q} -/
noncomputable def entropyCost (N q : ℕ) : ℝ :=
  (q : ℝ) * (1 + Real.log (N : ℝ) - Real.log (q : ℝ)) / Real.log 2

private theorem log_choose_le_entropy {N q : ℕ} (hq : 0 < q) (hqN : q ≤ N) :
    Real.log (N.choose q : ℝ) ≤
      (q : ℝ) * (1 + Real.log (N : ℝ) - Real.log (q : ℝ)) := by
  have hN : 0 < N := lt_of_lt_of_le hq hqN
  have hchoose : 0 < (N.choose q : ℝ) := by
    exact_mod_cast Nat.choose_pos hqN
  have hfactorial : 0 < (q.factorial : ℝ) := by
    exact_mod_cast q.factorial_pos
  have hlogChoose :
      Real.log (N.choose q : ℝ) ≤
        Real.log (((N : ℝ) ^ q) / (q.factorial : ℝ)) :=
    Real.log_le_log hchoose (Nat.choose_le_pow_div q N)
  have hlogFactorial := Stirling.le_log_factorial_stirling hq.ne'
  have hlogq : 0 ≤ Real.log (q : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hq)
  have hlogTwoPi : 0 ≤ Real.log (2 * Real.pi) := by
    apply Real.log_nonneg
    nlinarith [Real.two_le_pi]
  have hcoarse :
      (q : ℝ) * Real.log (q : ℝ) - (q : ℝ) ≤
        Real.log (q.factorial : ℝ) := by
    calc
      (q : ℝ) * Real.log (q : ℝ) - (q : ℝ) ≤
          (q : ℝ) * Real.log (q : ℝ) - (q : ℝ) +
            Real.log (q : ℝ) / 2 + Real.log (2 * Real.pi) / 2 := by
        linarith
      _ ≤ Real.log (q.factorial : ℝ) := hlogFactorial
  calc
    Real.log (N.choose q : ℝ) ≤
        Real.log (((N : ℝ) ^ q) / (q.factorial : ℝ)) := hlogChoose
    _ = (q : ℝ) * Real.log (N : ℝ) - Real.log (q.factorial : ℝ) := by
      rw [Real.log_div (pow_ne_zero q (Nat.cast_ne_zero.mpr hN.ne'))
        (ne_of_gt hfactorial), Real.log_pow]
    _ ≤ (q : ℝ) * Real.log (N : ℝ) -
        ((q : ℝ) * Real.log (q : ℝ) - (q : ℝ)) :=
      sub_le_sub_left hcoarse _
    _ = (q : ℝ) * (1 + Real.log (N : ℝ) - Real.log (q : ℝ)) := by ring


theorem logb_choose_le_entropyCost {N q : ℕ} (hq : 0 < q) (hqN : q ≤ N) :
    Real.logb 2 (N.choose q : ℝ) ≤ entropyCost N q := by
  have hlogTwo : 0 < Real.log 2 := Real.log_pos one_lt_two
  rw [Real.logb, entropyCost]
  exact div_le_div_of_nonneg_right (log_choose_le_entropy hq hqN) hlogTwo.le

private theorem fingerprintSize_pos
    {ε : ℝ} {n k : ℕ} (hε : 0 < ε) (hk : 2 ≤ k) (hnk : 2 * k + 1 ≤ n)
    (hRN : containerThreshold ε n k < vertexCount n k) :
    0 < fingerprintSize ε n k := by
  have hn : 0 < n := by omega
  have hnsub : 0 < n - k := by omega
  have hN : 0 < vertexCount n k := Nat.choose_pos (by omega)
  have hM : 0 < starSize n k := Nat.choose_pos (by omega)
  have hD : 0 < regularDegree n k := Nat.choose_pos (by omega)
  have hβ : 0 < densityParameter ε n k := by
    rw [densityParameter]
    positivity
  have hR : 0 < containerThreshold ε n k := by
    rw [containerThreshold]
    exact Nat.ceil_pos.mpr (by positivity)
  have hquotient :
      1 < (vertexCount n k : ℝ) / (containerThreshold ε n k : ℝ) := by
    apply (lt_div_iff₀ (by positivity)).2
    rw [one_mul]
    exact_mod_cast hRN
  rw [fingerprintSize]
  exact Nat.ceil_pos.mpr (mul_pos (inv_pos.mpr hβ) (Real.log_pos hquotient))


/-- # If q≤ N, R< (1+ε)M+1, and 1 + q + entropyCost≤ 2εM, then the aysmpototic bound holds.
-/
private theorem choose_mul_two_pow_le_rpow
    {ε : ℝ} {N M R q : ℕ}
    (hq : 0 < q) (hqN : q ≤ N)
    (hR : (R : ℝ) < (1 + ε) * (M : ℝ) + 1)
    (hlarge :
      1 + (q : ℝ) + entropyCost N q ≤ 2 * ε * (M : ℝ)) :
    (((N.choose q) * 2 ^ (R + q) : ℕ) : ℝ) ≤
      Real.rpow 2 ((1 + 3 * ε) * (M : ℝ)) := by
  have hchoose : 0 < (N.choose q : ℝ) := by
    exact_mod_cast Nat.choose_pos hqN
  have hlogb := logb_choose_le_entropyCost hq hqN
  have hexponent :
      Real.logb 2 (N.choose q : ℝ) + ((R + q : ℕ) : ℝ) ≤
        (1 + 3 * ε) * (M : ℝ) := by
    rw [Nat.cast_add]
    nlinarith
  rw [Nat.cast_mul, Nat.cast_pow]
  change (N.choose q : ℝ) * (2 : ℝ) ^ (R + q) ≤
    Real.rpow 2 ((1 + 3 * ε) * (M : ℝ))
  calc
    (N.choose q : ℝ) * (2 : ℝ) ^ (R + q) =
        Real.rpow 2 (Real.logb 2 (N.choose q : ℝ)) *
          Real.rpow 2 ((R + q : ℕ) : ℝ) := by
      congr 1
      · exact (Real.rpow_logb zero_lt_two one_lt_two.ne' hchoose).symm
      · exact (Real.rpow_natCast 2 (R + q)).symm
    _ = Real.rpow 2
        (Real.logb 2 (N.choose q : ℝ) + ((R + q : ℕ) : ℝ)) := by
      exact (Real.rpow_add zero_lt_two _ _).symm
    _ ≤ Real.rpow 2 ((1 + 3 * ε) * (M : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le one_le_two hexponent

/-- The finite container estimate and the entropy calculation give the desired counting bound. -/
theorem intersectingFamilyCount_le_of_entropy
    {ε : ℝ} {n k : ℕ} (hε : 0 < ε) (hk : 2 ≤ k) (hnk : 2 * k + 1 ≤ n)
    (hRN : containerThreshold ε n k < vertexCount n k)
    (hq : fingerprintSize ε n k ≤ vertexCount n k)
    (hlarge :
      1 + (fingerprintSize ε n k : ℝ) +
          entropyCost (vertexCount n k) (fingerprintSize ε n k) ≤
        2 * ε * (starSize n k : ℝ)) :
    (intersectingFamilyCount n k : ℝ) ≤
      Real.rpow 2 ((1 + 3 * ε) * (starSize n k : ℝ)) := by
  have hcontainer := kneser_containerHypotheses hε (by omega) hnk hq
  have hqpos := fingerprintSize_pos hε hk hnk hRN
  have hcount := intersectingFamilyCount_le (by omega : 0 < k) hcontainer
  have hcountReal :
      (intersectingFamilyCount n k : ℝ) ≤
        (((vertexCount n k).choose (fingerprintSize ε n k) *
          2 ^ (containerThreshold ε n k + fingerprintSize ε n k) : ℕ) : ℝ) := by
    exact_mod_cast hcount
  have hR :
      (containerThreshold ε n k : ℝ) <
        (1 + ε) * (starSize n k : ℝ) + 1 := by
    rw [containerThreshold]
    exact Nat.ceil_lt_add_one (by positivity)
  exact hcountReal.trans (choose_mul_two_pow_le_rpow hqpos hq hR hlarge)

/-! ## Uniform parameter estimates -/

private theorem self_le_choose_of_pos_of_lt {a r : ℕ} (hr : 0 < r) (hra : r < a) :
    a ≤ a.choose r := by
  have har : r ≤ a - 1 := by omega
  have hmono : r.choose (r - 1) ≤ (a - 1).choose (r - 1) :=
    Nat.choose_le_choose (r - 1) har
  have hrchoose : r.choose (r - 1) = r := by
    obtain ⟨s, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hr)
    rw [Nat.add_one_sub_one, Nat.choose_succ_self_right]
  have hid := Nat.choose_mul (n := a) (k := r) (s := 1) (by omega)
  rw [Nat.choose_one_right, Nat.choose_one_right] at hid
  rw [hrchoose] at hmono
  have hmul : a * r ≤ a.choose r * r := by
    rw [hid]
    exact Nat.mul_le_mul_left a hmono
  exact Nat.le_of_mul_le_mul_right hmul hr

private theorem choose_mul_index (n k : ℕ) (hk : 0 < k) :
    n.choose k * k = n * (n - 1).choose (k - 1) := by
  have h := Nat.choose_mul (n := n) (k := k) (s := 1) (by omega)
  rwa [Nat.choose_one_right, Nat.choose_one_right] at h

private theorem degree_cross_bound {n k : ℕ} (hk : 2 ≤ k) (hnk : 2 * k + 1 ≤ n) :
    n * (n - k) ≤ 3 * k * regularDegree n k := by
  have hindex : 0 < k - 1 := by omega
  have hindexlt : k - 1 < n - k - 1 := by omega
  have hchoose : n - k - 1 ≤ (n - k - 1).choose (k - 1) :=
    self_le_choose_of_pos_of_lt hindex hindexlt
  have hid := choose_mul_index (n - k) k (by omega)
  change (n - k).choose k * k =
    (n - k) * (n - k - 1).choose (k - 1) at hid
  change n * (n - k) ≤ 3 * k * (n - k).choose k
  calc
    n * (n - k) ≤ (3 * (n - k - 1)) * (n - k) :=
      Nat.mul_le_mul_right (n - k) (by omega)
    _ ≤ (3 * (n - k - 1).choose (k - 1)) * (n - k) :=
      Nat.mul_le_mul_right (n - k) (Nat.mul_le_mul_left 3 hchoose)
    _ = 3 * ((n - k) * (n - k - 1).choose (k - 1)) := by ring
    _ = 3 * ((n - k).choose k * k) := by rw [hid]
    _ = 3 * k * (n - k).choose k := by ring

private theorem starSize_ge_sub_one {n k : ℕ} (hk : 2 ≤ k) (hnk : 2 * k + 1 ≤ n) :
    n - 1 ≤ starSize n k := by
  exact self_le_choose_of_pos_of_lt (by omega) (by omega)

private theorem twice_starSize_lt_vertexCount
    {n k : ℕ} (hk : 2 ≤ k) (hnk : 2 * k + 1 ≤ n) :
    2 * starSize n k < vertexCount n k := by
  have hM : 0 < starSize n k := Nat.choose_pos (by omega)
  have hNM := choose_mul_index n k (by omega)
  change vertexCount n k * k = n * starSize n k at hNM
  apply Nat.lt_of_mul_lt_mul_right
  calc
    2 * starSize n k * k = 2 * k * starSize n k := by ring
    _ < n * starSize n k := Nat.mul_lt_mul_of_pos_right (by omega) hM
    _ = vertexCount n k * k := hNM.symm

/-- The rounded container threshold is strictly smaller than the Kneser vertex count. -/
private theorem containerThreshold_lt_vertexCount
    {ε : ℝ} {n k : ℕ} (hεone : ε < 1) (hk : 2 ≤ k) (hnk : 2 * k + 1 ≤ n) :
    containerThreshold ε n k < vertexCount n k := by
  have hM : 0 < starSize n k := Nat.choose_pos (by omega)
  have hR : containerThreshold ε n k ≤ 2 * starSize n k := by
    rw [containerThreshold]
    apply Nat.ceil_le.mpr
    rw [Nat.cast_mul, Nat.cast_ofNat]
    nlinarith
  exact hR.trans_lt (twice_starSize_lt_vertexCount hk hnk)

private theorem starSize_le_vertexCount {n k : ℕ} (hk : 0 < k) (hnk : k ≤ n) :
    starSize n k ≤ vertexCount n k := by
  rw [starSize, vertexCount, Nat.choose_eq_choose_pred_add (by omega) hk]
  exact Nat.le_add_right _ _

private theorem vertexCount_le_n_mul_starSize {n k : ℕ} (hk : 0 < k) :
    vertexCount n k ≤ n * starSize n k := by
  have hNMnat := choose_mul_index n k hk
  change vertexCount n k * k = n * starSize n k at hNMnat
  calc
    vertexCount n k = vertexCount n k * 1 := by rw [Nat.mul_one]
    _ ≤ vertexCount n k * k := Nat.mul_le_mul_left _ hk
    _ = n * starSize n k := hNMnat

/-- bound for β^{-1}
-/
private theorem densityParameter_inv_le
    {ε : ℝ} {n k : ℕ} (hε : 0 < ε) (hk : 2 ≤ k) (hnk : 2 * k + 1 ≤ n) :
    (densityParameter ε n k)⁻¹ ≤
      3 * ((1 + ε) / ε) * (starSize n k : ℝ) / (n : ℝ) := by
  have hn : 0 < n := by omega
  have hnsub : 0 < n - k := by omega
  have hD : 0 < regularDegree n k := Nat.choose_pos (by omega)
  have hNMnat := choose_mul_index n k (by omega)
  change vertexCount n k * k = n * starSize n k at hNMnat
  have hNM :
      (vertexCount n k : ℝ) * (k : ℝ) = (n : ℝ) * (starSize n k : ℝ) := by
    exact_mod_cast hNMnat
  have hdegree :
      (n : ℝ) * ((n - k : ℕ) : ℝ) ≤
        3 * (k : ℝ) * (regularDegree n k : ℝ) := by
    exact_mod_cast degree_cross_bound hk hnk
  have hcross :
      (((vertexCount n k : ℝ) * ((n - k : ℕ) : ℝ)) * (n : ℝ)) * (k : ℝ) ≤
        ((3 * (starSize n k : ℝ)) * ((regularDegree n k : ℝ) * (n : ℝ))) *
          (k : ℝ) := by
    calc
      (((vertexCount n k : ℝ) * ((n - k : ℕ) : ℝ)) * (n : ℝ)) * (k : ℝ) =
          ((vertexCount n k : ℝ) * (k : ℝ)) *
            ((n : ℝ) * ((n - k : ℕ) : ℝ)) := by ring
      _ = ((n : ℝ) * (starSize n k : ℝ)) *
            ((n : ℝ) * ((n - k : ℕ) : ℝ)) := by rw [hNM]
      _ ≤ ((n : ℝ) * (starSize n k : ℝ)) *
            (3 * (k : ℝ) * (regularDegree n k : ℝ)) :=
        mul_le_mul_of_nonneg_left hdegree (by positivity)
      _ = ((3 * (starSize n k : ℝ)) *
            ((regularDegree n k : ℝ) * (n : ℝ))) * (k : ℝ) := by ring
  have hfraction :
      ((vertexCount n k : ℝ) * ((n - k : ℕ) : ℝ)) /
          ((regularDegree n k : ℝ) * (n : ℝ)) ≤
        (3 * (starSize n k : ℝ)) / (n : ℝ) := by
    apply (div_le_div_iff₀ (by positivity : 0 < (regularDegree n k : ℝ) * (n : ℝ))
      (by positivity : 0 < (n : ℝ))).2
    exact le_of_mul_le_mul_right hcross (by positivity : 0 < (k : ℝ))
  rw [densityParameter, mul_inv_rev, inv_div, inv_div]
  calc
    ((vertexCount n k : ℝ) * ((n - k : ℕ) : ℝ)) /
          ((regularDegree n k : ℝ) * (n : ℝ)) * ((1 + ε) / ε) =
        ((1 + ε) / ε) *
          (((vertexCount n k : ℝ) * ((n - k : ℕ) : ℝ)) /
            ((regularDegree n k : ℝ) * (n : ℝ))) := by ring
    _ ≤ ((1 + ε) / ε) * ((3 * (starSize n k : ℝ)) / (n : ℝ)) :=
      mul_le_mul_of_nonneg_left hfraction (by positivity)
    _ = 3 * ((1 + ε) / ε) * (starSize n k : ℝ) / (n : ℝ) := by ring

private noncomputable def ratioConstant (ε : ℝ) : ℝ :=
  2 + 3 * ((1 + ε) / ε)

private noncomputable def fingerprintRatioBound (ε : ℝ) (n : ℕ) : ℝ :=
  ratioConstant ε * (1 + Real.log (n : ℝ)) / (n : ℝ)

private noncomputable def entropyNumerator (N x : ℝ) : ℝ :=
  x * (1 + Real.log N - Real.log x)

private theorem entropyNumerator_mono {N x y : ℝ}
    (hx : 0 < x) (hxy : x ≤ y) (hyN : y ≤ N) :
    entropyNumerator N x ≤ entropyNumerator N y := by
  have hy : 0 < y := hx.trans_le hxy
  have hN : 0 < N := hy.trans_le hyN
  have hlogNy : 0 ≤ Real.log N - Real.log y := by
    exact sub_nonneg.mpr (Real.strictMonoOn_log.monotoneOn hy hN hyN)
  have hratio : 0 < y / x := div_pos hy hx
  have hlogratio := Real.log_le_sub_one_of_pos hratio
  have hscaled : x * Real.log (y / x) ≤ y - x := by
    calc
      x * Real.log (y / x) ≤ x * (y / x - 1) :=
        mul_le_mul_of_nonneg_left hlogratio hx.le
      _ = x * (y / x) - x := by ring
      _ = y - x := by rw [mul_div_cancel₀ y hx.ne']
  rw [Real.log_div hy.ne' hx.ne'] at hscaled
  have hfactor : y - x ≤ (y - x) * (1 + Real.log N - Real.log y) := by
    calc
      y - x ≤ (y - x) + (y - x) * (Real.log N - Real.log y) :=
        le_add_of_nonneg_right (mul_nonneg (sub_nonneg.mpr hxy) hlogNy)
      _ = (y - x) * (1 + Real.log N - Real.log y) := by ring
  rw [entropyNumerator, entropyNumerator]
  calc
    x * (1 + Real.log N - Real.log x) =
        x * (1 + Real.log N - Real.log y) + x * (Real.log y - Real.log x) := by ring
    _ ≤ x * (1 + Real.log N - Real.log y) + (y - x) :=
      add_le_add_right hscaled _
    _ = (y - x) + x * (1 + Real.log N - Real.log y) := by ring
    _ ≤ (y - x) * (1 + Real.log N - Real.log y) +
        x * (1 + Real.log N - Real.log y) :=
      add_le_add_left hfactor _
    _ = y * (1 + Real.log N - Real.log y) := by ring

private theorem ceil_inv_mul_log_lt_add_one {β z B L : ℝ}
    (hβ : 0 < β) (hB : β⁻¹ ≤ B) (hz : 1 < z)
    (hzL : Real.log z ≤ L) :
    (⌈β⁻¹ * Real.log z⌉₊ : ℝ) < B * L + 1 := by
  have hz0 : 0 ≤ Real.log z := (Real.log_pos hz).le
  have hB0 : 0 ≤ B := (inv_pos.mpr hβ).le.trans hB
  calc
    (⌈β⁻¹ * Real.log z⌉₊ : ℝ) < β⁻¹ * Real.log z + 1 :=
      Nat.ceil_lt_add_one (mul_nonneg (inv_nonneg.mpr hβ.le) hz0)
    _ ≤ B * L + 1 := add_le_add (mul_le_mul hB hzL hz0 hB0) le_rfl


/-- bound for q.
-/
private theorem fingerprintSize_lt_star_mul_ratioBound
    {ε : ℝ} {n k : ℕ} (hε : 0 < ε) (hk : 2 ≤ k) (hnk : 2 * k + 1 ≤ n)
    (hRN : containerThreshold ε n k < vertexCount n k) :
    (fingerprintSize ε n k : ℝ) <
      (starSize n k : ℝ) * fingerprintRatioBound ε n := by
  have hnOne : (1 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 1 < n)
  have hN : 0 < vertexCount n k := Nat.choose_pos (by omega)
  have hM : 0 < starSize n k := Nat.choose_pos (by omega)
  have hD : 0 < regularDegree n k := Nat.choose_pos (by omega)
  have hnsub : 0 < n - k := by omega
  have hβ : 0 < densityParameter ε n k := by
    rw [densityParameter]
    positivity
  have hR : 0 < containerThreshold ε n k := by
    rw [containerThreshold]
    exact Nat.ceil_pos.mpr (by positivity)
  have hMR : (starSize n k : ℝ) ≤ (containerThreshold ε n k : ℝ) := by
    calc
      (starSize n k : ℝ) = 1 * (starSize n k : ℝ) := by rw [one_mul]
      _ ≤ (1 + ε) * (starSize n k : ℝ) :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ ≤ (containerThreshold ε n k : ℝ) := Nat.le_ceil _
  have hNleNR :
      (vertexCount n k : ℝ) ≤ (n : ℝ) * (containerThreshold ε n k : ℝ) := by
    calc
      (vertexCount n k : ℝ) ≤ (n : ℝ) * (starSize n k : ℝ) := by
        exact_mod_cast vertexCount_le_n_mul_starSize (by omega : 0 < k)
      _ ≤ (n : ℝ) * (containerThreshold ε n k : ℝ) :=
        mul_le_mul_of_nonneg_left hMR (by positivity)
  have hquotientLe :
      (vertexCount n k : ℝ) / (containerThreshold ε n k : ℝ) ≤ (n : ℝ) := by
    exact (div_le_iff₀ (by positivity : 0 < (containerThreshold ε n k : ℝ))).2 hNleNR
  have hquotientOne :
      1 < (vertexCount n k : ℝ) / (containerThreshold ε n k : ℝ) := by
    apply (lt_div_iff₀ (by positivity)).2
    rw [one_mul]
    exact_mod_cast hRN
  have hlogLe :
      Real.log ((vertexCount n k : ℝ) / (containerThreshold ε n k : ℝ)) ≤
        Real.log (n : ℝ) :=
    Real.log_le_log (by positivity) hquotientLe
  have hlogn : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hnOne.le
  have hceil := ceil_inv_mul_log_lt_add_one hβ
    (densityParameter_inv_le hε hk hnk) hquotientOne hlogLe
  have hnTwoM : n ≤ 2 * starSize n k := by
    have hMlower := starSize_ge_sub_one hk hnk
    omega
  have honeLe : (1 : ℝ) ≤ 2 * (starSize n k : ℝ) / (n : ℝ) := by
    apply (le_div_iff₀ (by positivity)).2
    rw [one_mul]
    exact_mod_cast hnTwoM
  have hc : 0 < (1 + ε) / ε := by positivity
  change (fingerprintSize ε n k : ℝ) < _
  change (fingerprintSize ε n k : ℝ) <
    (3 * ((1 + ε) / ε) * (starSize n k : ℝ) / (n : ℝ)) *
      Real.log (n : ℝ) + 1 at hceil
  calc
    (fingerprintSize ε n k : ℝ) <
        (3 * ((1 + ε) / ε) * (starSize n k : ℝ) / (n : ℝ)) *
          Real.log (n : ℝ) + 1 := hceil
    _ ≤ (3 * ((1 + ε) / ε) * (starSize n k : ℝ) / (n : ℝ)) *
          Real.log (n : ℝ) + 2 * (starSize n k : ℝ) / (n : ℝ) :=
      by linarith
    _ = ((starSize n k : ℝ) / (n : ℝ)) *
          (2 + 3 * ((1 + ε) / ε) * Real.log (n : ℝ)) := by ring
    _ ≤ ((starSize n k : ℝ) / (n : ℝ)) *
          ((2 + 3 * ((1 + ε) / ε)) * (1 + Real.log (n : ℝ))) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      nlinarith
    _ = (starSize n k : ℝ) * fingerprintRatioBound ε n := by
      rw [fingerprintRatioBound, ratioConstant]
      ring

private theorem inv_sub_one_le_fingerprintRatioBound
    {ε : ℝ} (hε : 0 < ε) {n : ℕ} (hn : 2 ≤ n) :
    1 / ((n : ℝ) - 1) ≤ fingerprintRatioBound ε n := by
  have hnReal : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnPos : (0 : ℝ) < (n : ℝ) := by positivity
  have hnSubPos : (0 : ℝ) < (n : ℝ) - 1 := by linarith
  have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by linarith)
  have hc : 0 < (1 + ε) / ε := by positivity
  have hinv : 1 / ((n : ℝ) - 1) ≤ 2 / (n : ℝ) := by
    apply (div_le_div_iff₀ hnSubPos hnPos).2
    linarith
  calc
    1 / ((n : ℝ) - 1) ≤ 2 / (n : ℝ) := hinv
    _ ≤ ratioConstant ε * (1 + Real.log (n : ℝ)) / (n : ℝ) := by
      apply div_le_div_of_nonneg_right _ hnPos.le
      rw [ratioConstant]
      nlinarith
    _ = fingerprintRatioBound ε n := by rw [fingerprintRatioBound]

/-- bound for entropyCost.
-/
private theorem entropyCost_le_star_mul_ratioBound
    {ε : ℝ} {n k : ℕ} (hε : 0 < ε) (hk : 2 ≤ k) (hnk : 2 * k + 1 ≤ n)
    (hRN : containerThreshold ε n k < vertexCount n k)
    (hratio : fingerprintRatioBound ε n ≤ 1) :
    entropyCost (vertexCount n k) (fingerprintSize ε n k) ≤
      (starSize n k : ℝ) * fingerprintRatioBound ε n *
        (1 + 2 * Real.log (n : ℝ)) / Real.log 2 := by
  have hnOne : (1 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 1 < n)
  have hN : 0 < vertexCount n k := Nat.choose_pos (by omega)
  have hM : 0 < starSize n k := Nat.choose_pos (by omega)
  have hratioPos : 0 < fingerprintRatioBound ε n := by
    rw [fingerprintRatioBound, ratioConstant]
    positivity
  have hq : 0 < (fingerprintSize ε n k : ℝ) := by
    exact_mod_cast fingerprintSize_pos hε hk hnk hRN
  have hqQ :
      (fingerprintSize ε n k : ℝ) ≤
        (starSize n k : ℝ) * fingerprintRatioBound ε n :=
    (fingerprintSize_lt_star_mul_ratioBound hε hk hnk hRN).le
  have hQpos :
      0 < (starSize n k : ℝ) * fingerprintRatioBound ε n :=
    mul_pos (by positivity) hratioPos
  have hQleN :
      (starSize n k : ℝ) * fingerprintRatioBound ε n ≤
        (vertexCount n k : ℝ) := by
    calc
      (starSize n k : ℝ) * fingerprintRatioBound ε n ≤
          (starSize n k : ℝ) * 1 :=
        mul_le_mul_of_nonneg_left hratio (by positivity)
      _ = (starSize n k : ℝ) := by rw [mul_one]
      _ ≤ (vertexCount n k : ℝ) := by
        exact_mod_cast starSize_le_vertexCount (by omega : 0 < k) (by omega : k ≤ n)
  have hmono := entropyNumerator_mono hq hqQ hQleN
  have hNleNM :
      (vertexCount n k : ℝ) ≤ (n : ℝ) * (starSize n k : ℝ) := by
    exact_mod_cast vertexCount_le_n_mul_starSize (by omega : 0 < k)
  have hlogN :
      Real.log (vertexCount n k : ℝ) ≤
        Real.log (n : ℝ) + Real.log (starSize n k : ℝ) := by
    calc
      Real.log (vertexCount n k : ℝ) ≤
          Real.log ((n : ℝ) * (starSize n k : ℝ)) :=
        Real.log_le_log (by positivity) hNleNM
      _ = Real.log (n : ℝ) + Real.log (starSize n k : ℝ) := by
        rw [Real.log_mul (by positivity) (by positivity)]
  have hratioLower := inv_sub_one_le_fingerprintRatioBound hε (by omega : 2 ≤ n)
  have hlogRatioLower :
      -Real.log ((n : ℝ) - 1) ≤ Real.log (fingerprintRatioBound ε n) := by
    have h := Real.log_le_log (by positivity : 0 < 1 / ((n : ℝ) - 1)) hratioLower
    rw [one_div, Real.log_inv] at h
    exact h
  have hlogSub : Real.log ((n : ℝ) - 1) ≤ Real.log (n : ℝ) := by
    exact Real.log_le_log (sub_pos.mpr hnOne) (by linarith)
  have hlogQ :
      Real.log ((starSize n k : ℝ) * fingerprintRatioBound ε n) =
        Real.log (starSize n k : ℝ) + Real.log (fingerprintRatioBound ε n) := by
    rw [Real.log_mul (by positivity) hratioPos.ne']
  have hbracket :
      1 + Real.log (vertexCount n k : ℝ) -
          Real.log ((starSize n k : ℝ) * fingerprintRatioBound ε n) ≤
        1 + 2 * Real.log (n : ℝ) := by
    rw [hlogQ]
    linarith
  have hnumerator :
      entropyNumerator (vertexCount n k : ℝ) (fingerprintSize ε n k : ℝ) ≤
        ((starSize n k : ℝ) * fingerprintRatioBound ε n) *
          (1 + 2 * Real.log (n : ℝ)) := by
    exact hmono.trans (mul_le_mul_of_nonneg_left hbracket hQpos.le)
  change entropyNumerator (vertexCount n k : ℝ) (fingerprintSize ε n k : ℝ) /
      Real.log 2 ≤
    (starSize n k : ℝ) * fingerprintRatioBound ε n *
      (1 + 2 * Real.log (n : ℝ)) / Real.log 2
  exact div_le_div_of_nonneg_right hnumerator (Real.log_pos one_lt_two).le

private noncomputable def asymptoticError (ε : ℝ) (n : ℕ) : ℝ :=
  fingerprintRatioBound ε n *
    (2 + (1 + 2 * Real.log (n : ℝ)) / Real.log 2)

private noncomputable def entropyConstant : ℝ :=
  2 + 2 / Real.log 2

private theorem asymptoticError_le
    {ε : ℝ} (hε : 0 < ε) {n : ℕ} (hn : 2 ≤ n) :
    asymptoticError ε n ≤
      ratioConstant ε * entropyConstant *
        ((1 + Real.log (n : ℝ)) ^ 2 / (n : ℝ)) := by
  have hnReal : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnPos : (0 : ℝ) < (n : ℝ) := by positivity
  have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by linarith)
  have hfactor :
      2 + (1 + 2 * Real.log (n : ℝ)) / Real.log 2 ≤
        entropyConstant * (1 + Real.log (n : ℝ)) := by
    have hlogTwo : 0 < Real.log 2 := Real.log_pos one_lt_two
    rw [entropyConstant]
    calc
      2 + (1 + 2 * Real.log (n : ℝ)) / Real.log 2 ≤
          2 * (1 + Real.log (n : ℝ)) +
            (2 * (1 + Real.log (n : ℝ))) / Real.log 2 :=
        add_le_add (by nlinarith)
          (div_le_div_of_nonneg_right (by nlinarith) hlogTwo.le)
      _ = (2 + 2 / Real.log 2) * (1 + Real.log (n : ℝ)) := by ring
  have hratioConstant : 0 ≤ ratioConstant ε := by
    rw [ratioConstant]
    positivity
  rw [asymptoticError, fingerprintRatioBound]
  calc
    ratioConstant ε * (1 + Real.log (n : ℝ)) / (n : ℝ) *
          (2 + (1 + 2 * Real.log (n : ℝ)) / Real.log 2) ≤
        (ratioConstant ε * (1 + Real.log (n : ℝ)) / (n : ℝ)) *
          (entropyConstant * (1 + Real.log (n : ℝ))) :=
      mul_le_mul_of_nonneg_left hfactor (by positivity)
    _ = ratioConstant ε * entropyConstant *
          ((1 + Real.log (n : ℝ)) ^ 2 / (n : ℝ)) := by ring

/-- # The third condition.
-/
private theorem entropy_error_bound
    {ε : ℝ} {n k : ℕ} (hε : 0 < ε) (hk : 2 ≤ k) (hnk : 2 * k + 1 ≤ n)
    (hRN : containerThreshold ε n k < vertexCount n k)
    (hratio : fingerprintRatioBound ε n ≤ 1)
    (herror : asymptoticError ε n ≤ 2 * ε) :
    1 + (fingerprintSize ε n k : ℝ) +
        entropyCost (vertexCount n k) (fingerprintSize ε n k) ≤
      2 * ε * (starSize n k : ℝ) := by
  have hnOne : (1 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 1 < n)
  have hM : 0 < starSize n k := Nat.choose_pos (by omega)
  have hratioPos : 0 < fingerprintRatioBound ε n := by
    rw [fingerprintRatioBound, ratioConstant]
    positivity
  have hratioLower := inv_sub_one_le_fingerprintRatioBound hε (by omega : 2 ≤ n)
  have hone :
      (1 : ℝ) ≤ (starSize n k : ℝ) * fingerprintRatioBound ε n := by
    have hMlower : ((n - 1 : ℕ) : ℝ) ≤ (starSize n k : ℝ) := by
      exact_mod_cast starSize_ge_sub_one hk hnk
    have honeM :
        (1 : ℝ) ≤ (starSize n k : ℝ) / ((n : ℝ) - 1) := by
      apply (le_div_iff₀ (sub_pos.mpr hnOne)).2
      rw [one_mul, ← Nat.cast_one, ← Nat.cast_sub (by omega : 1 ≤ n)]
      exact hMlower
    exact honeM.trans (by
      calc
        (starSize n k : ℝ) / ((n : ℝ) - 1) =
            (starSize n k : ℝ) * (1 / ((n : ℝ) - 1)) := by ring
        _ ≤ (starSize n k : ℝ) * fingerprintRatioBound ε n :=
          mul_le_mul_of_nonneg_left hratioLower (by positivity))
  have hq := (fingerprintSize_lt_star_mul_ratioBound hε hk hnk hRN).le
  have hentropy := entropyCost_le_star_mul_ratioBound hε hk hnk hRN hratio
  have hsum :
      1 + (fingerprintSize ε n k : ℝ) +
          entropyCost (vertexCount n k) (fingerprintSize ε n k) ≤
        (starSize n k : ℝ) * asymptoticError ε n := by
    calc
      1 + (fingerprintSize ε n k : ℝ) +
          entropyCost (vertexCount n k) (fingerprintSize ε n k) ≤
          (starSize n k : ℝ) * fingerprintRatioBound ε n +
            (starSize n k : ℝ) * fingerprintRatioBound ε n +
              ((starSize n k : ℝ) * fingerprintRatioBound ε n *
                (1 + 2 * Real.log (n : ℝ)) / Real.log 2) := by
        linarith
      _ = (starSize n k : ℝ) * asymptoticError ε n := by
        rw [asymptoticError]
        ring
  calc
    1 + (fingerprintSize ε n k : ℝ) +
        entropyCost (vertexCount n k) (fingerprintSize ε n k) ≤
      (starSize n k : ℝ) * asymptoticError ε n := hsum
    _ ≤ (starSize n k : ℝ) * (2 * ε) :=
      mul_le_mul_of_nonneg_left herror (by positivity)
    _ = 2 * ε * (starSize n k : ℝ) := by ring


/-- # Choose n_0 big enough.
-/
private theorem eventually_one_add_log_sq_div_lt {δ : ℝ} (hδ : 0 < δ) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      (1 + Real.log (n : ℝ)) ^ 2 / (n : ℝ) < δ := by
  have hreal :
      Tendsto (fun x : ℝ => (1 + Real.log x) ^ 2 / x) atTop (nhds 0) := by
    have hsq := Real.isLittleO_pow_log_id_atTop (n := 2)
    have hlog := Real.isLittleO_log_id_atTop.const_mul_left 2
    have hone := isLittleO_const_id_atTop (1 : ℝ)
    have hsum := hsq.add (hlog.add hone)
    have hsmall : (fun x : ℝ => (1 + Real.log x) ^ 2) =o[atTop] id := by
      refine hsum.congr_left ?_
      intro x
      ring
    exact hsmall.tendsto_div_nhds_zero
  have hnat :
      Tendsto (fun n : ℕ => (1 + Real.log (n : ℝ)) ^ 2 / (n : ℝ)) atTop (nhds 0) :=
    hreal.comp tendsto_natCast_atTop_atTop
  have hevent := hnat.eventually (Iio_mem_nhds hδ)
  rw [eventually_atTop] at hevent
  exact hevent

/-- For fixed `0 < ε < 1`, both finite error conditions needed by the container estimate hold
uniformly for all `k ≥ 2` once `n` is sufficiently large. -/
theorem eventually_fingerprint_bounds (ε : ℝ) (hε : 0 < ε) (hεone : ε < 1) :
    ∃ n₀ : ℕ, ∀ n k : ℕ, n₀ ≤ n → 2 ≤ k → 2 * k + 1 ≤ n →
      fingerprintSize ε n k ≤ vertexCount n k ∧
        1 + (fingerprintSize ε n k : ℝ) +
            entropyCost (vertexCount n k) (fingerprintSize ε n k) ≤
          2 * ε * (starSize n k : ℝ) := by
  have hC : 0 < ratioConstant ε := by
    rw [ratioConstant]
    positivity
  have hB : 0 < entropyConstant := by
    rw [entropyConstant]
    have hlogTwo : 0 < Real.log 2 := Real.log_pos one_lt_two
    positivity
  have hCB : 0 < ratioConstant ε * entropyConstant := mul_pos hC hB
  let δ := (2 * ε) / (ratioConstant ε * entropyConstant)
  have hδ : 0 < δ := by
    exact div_pos (by positivity) hCB
  obtain ⟨n₁, hn₁⟩ := eventually_one_add_log_sq_div_lt hδ
  refine ⟨max 2 n₁, ?_⟩
  intro n k hn hk hnk
  have hnTwo : 2 ≤ n := (le_max_left 2 n₁).trans hn
  have hn₁n : n₁ ≤ n := (le_max_right 2 n₁).trans hn
  have hsquare := hn₁ n hn₁n
  have hnReal : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hnTwo
  have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by linarith)
  have herror : asymptoticError ε n ≤ 2 * ε := by
    apply le_of_lt
    calc
      asymptoticError ε n ≤
            ratioConstant ε * entropyConstant *
              ((1 + Real.log (n : ℝ)) ^ 2 / (n : ℝ)) :=
          asymptoticError_le hε hnTwo
      _ < (ratioConstant ε * entropyConstant) *
            ((2 * ε) / (ratioConstant ε * entropyConstant)) :=
          mul_lt_mul_of_pos_left hsquare hCB
      _ = 2 * ε := mul_div_cancel₀ _ hCB.ne'
  have hratioNonneg : 0 ≤ fingerprintRatioBound ε n := by
    rw [fingerprintRatioBound, ratioConstant]
    positivity
  have hfactorTwo :
      2 ≤ 2 + (1 + 2 * Real.log (n : ℝ)) / Real.log 2 := by
    exact le_add_of_nonneg_right (div_nonneg (by linarith) (Real.log_pos one_lt_two).le)
  have htwoRatio : 2 * fingerprintRatioBound ε n ≤ asymptoticError ε n := by
    calc
      2 * fingerprintRatioBound ε n = fingerprintRatioBound ε n * 2 := by ring
      _ ≤ fingerprintRatioBound ε n *
          (2 + (1 + 2 * Real.log (n : ℝ)) / Real.log 2) :=
        mul_le_mul_of_nonneg_left hfactorTwo hratioNonneg
      _ = asymptoticError ε n := by rw [asymptoticError]
  have hratioOne : fingerprintRatioBound ε n < 1 := by
    nlinarith
  have hRN := containerThreshold_lt_vertexCount hεone hk hnk
  have hM : 0 < starSize n k := Nat.choose_pos (by omega)
  have hqReal :
      (fingerprintSize ε n k : ℝ) < (vertexCount n k : ℝ) := by
    calc
      (fingerprintSize ε n k : ℝ) <
          (starSize n k : ℝ) * fingerprintRatioBound ε n :=
        fingerprintSize_lt_star_mul_ratioBound hε hk hnk hRN
      _ < (starSize n k : ℝ) * 1 :=
        mul_lt_mul_of_pos_left hratioOne (by exact_mod_cast hM)
      _ = (starSize n k : ℝ) := by rw [mul_one]
      _ ≤ (vertexCount n k : ℝ) := by
        exact_mod_cast starSize_le_vertexCount (by omega : 0 < k) (by omega : k ≤ n)
  have hqN : fingerprintSize ε n k ≤ vertexCount n k := by
    exact_mod_cast hqReal.le
  exact ⟨hqN, entropy_error_bound hε hk hnk hRN hratioOne.le herror⟩

/-- Every subfamily of a full star is intersecting. -/
theorem intersectingFamilyCount_lower_bound
    {n k : ℕ} (hk : 2 ≤ k) (hnk : 2 * k + 1 ≤ n) :
    2 ^ starSize n k ≤ intersectingFamilyCount n k := by
  exact pow_starSize_le_intersectingFamilyCount (by omega) (by omega)

/-- # Main Theorem -/
theorem eventually_intersectingFamilyCount_le
    (ε : ℝ) (hε : 0 < ε) (hεone : ε < 1) :
    ∃ n₀ : ℕ, ∀ n k : ℕ, n₀ < n → 2 ≤ k → 2 * k + 1 ≤ n →
      (intersectingFamilyCount n k : ℝ) ≤
        Real.rpow 2 ((1 + 3 * ε) * (starSize n k : ℝ)) := by
  obtain ⟨n₀, hparams⟩ := eventually_fingerprint_bounds ε hε hεone
  refine ⟨n₀, ?_⟩
  intro n k hn hk hnk
  obtain ⟨hq, hlarge⟩ := hparams n k hn.le hk hnk
  exact intersectingFamilyCount_le_of_entropy hε hk hnk
    (containerThreshold_lt_vertexCount hεone hk hnk) hq hlarge

end SimpleGraph.KneserCounting
