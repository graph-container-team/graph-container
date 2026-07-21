/-
Copyright (c) 2026 Graph Container formalization team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Graph Container formalization team
-/
module

public import GraphContainer.Intersecting.Spectrum
public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
public import Mathlib.Data.Real.Basic

import Mathlib.Analysis.Matrix.Order
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

/-!
# Supersaturation in Kneser graphs

This file proves the spectral mixing estimate (Theorem 2.5) and derives Proposition 2.7 from the
Kneser least-eigenvalue formula cited as Theorem 2.6 in the paper.  That formula is proved in
`GraphContainer.Intersecting.Spectrum`; the conditional intermediate theorem is retained because
it cleanly separates the generic spectral calculation from the Kneser spectrum.

## Main results

* `SimpleGraph.expander_mixing_induced_edge_count`: a lower bound on the number of edges induced
  by a vertex set in a regular graph.
* `SimpleGraph.KneserCounting.isRegularOfDegree_graph`: the degree of a Kneser graph.
* `SimpleGraph.KneserCounting.kneser_supersaturation_of_isLeast`: Proposition 2.7, conditional on
  the least-eigenvalue formula from Theorem 2.6.
* `SimpleGraph.KneserCounting.kneser_supersaturation`: the unconditional Proposition 2.7.
-/

@[expose] public section

open Finset

namespace SimpleGraph

/-- A lower bound on the spectrum of a real Hermitian matrix gives the corresponding lower bound
on its quadratic form. -/
private lemma min_spectrum_mul_dotProduct_le_of_isHermitian
    {ι : Type*} [Fintype ι] [DecidableEq ι] {A : Matrix ι ι ℝ} (hA : A.IsHermitian)
    {a : ℝ} (ha : IsLeast (spectrum ℝ A) a) (x : ι → ℝ) :
    a * dotProduct x x ≤ dotProduct x (Matrix.mulVec A x) := by
  open scoped MatrixOrder in
    have hle :
        algebraMap ℝ (Matrix ι ι ℝ) a ≤ A :=
      algebraMap_le_of_le_spectrum ha.2 hA
    have hquad := hle.dotProduct_mulVec_nonneg x
    have hdiag :
        algebraMap ℝ (Matrix ι ι ℝ) a = Matrix.diagonal (fun _ ↦ a) := by
      ext i j
      simp [Matrix.algebraMap_eq_diagonal, Pi.algebraMap_apply, Matrix.diagonal_apply]
    rw [hdiag] at hquad
    simp only [Matrix.sub_mulVec, dotProduct_sub] at hquad
    simpa [dotProduct, Matrix.mulVec, Matrix.diagonal_apply, mul_sum, mul_comm,
      mul_left_comm, mul_assoc] using hquad

/-- The adjacency quadratic form of the indicator of `S` is twice the number of edges induced by
`S`. -/
private lemma indicator_dotProduct_adjMatrix_indicator
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) :
    let χ : V → ℝ := fun v ↦ if v ∈ S then 1 else 0
    dotProduct χ (Matrix.mulVec (G.adjMatrix ℝ) χ) =
      (2 * #(G.induce (S : Set V)).edgeFinset : ℝ) := by
  classical
  letI : Fintype (S : Set V) := FinsetCoe.fintype S
  dsimp
  have hnat :
      ∑ x ∈ S, #(S.filter fun y ↦ G.Adj x y) =
        2 * #(G.induce (S : Set V)).edgeFinset := by
    calc
      ∑ x ∈ S, #(S.filter fun y ↦ G.Adj x y) =
          ∑ x : (S : Set V), (G.induce (S : Set V)).degree x := by
            rw [← S.sum_attach]
            have hatt : S.attach = (Finset.univ : Finset (S : Set V)) := by
              ext x
              simp
            rw [hatt]
            apply Finset.sum_congr rfl
            intro x _
            rw [← SimpleGraph.card_neighborFinset_eq_degree]
            have heq :
                S.filter (fun y ↦ G.Adj x y) =
                  ((G.induce (S : Set V)).neighborFinset x).map
                    (Function.Embedding.subtype fun x ↦ x ∈ (S : Set V)) := by
              ext y
              simp [and_comm]
            rw [heq, Finset.card_map]
      _ = 2 * #(G.induce (S : Set V)).edgeFinset :=
        (G.induce (S : Set V)).sum_degrees_eq_twice_card_edges
  calc
    dotProduct (fun v ↦ if v ∈ S then 1 else 0)
        (Matrix.mulVec (G.adjMatrix ℝ) (fun v ↦ if v ∈ S then 1 else 0)) =
        ((∑ x ∈ S, #(S.filter fun y ↦ G.Adj x y) : ℕ) : ℝ) := by
      simp [dotProduct, Matrix.mulVec, SimpleGraph.adjMatrix]
    _ = (2 * #(G.induce (S : Set V)).edgeFinset : ℝ) := by
      exact_mod_cast hnat

/-- **Theorem 2.5 (spectral estimate).**

The least adjacency eigenvalue controls the number of edges induced by every vertex set in a
regular graph.
-/
theorem expander_mixing_induced_edge_count
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {D : ℕ} {lam : ℝ}
    (hreg : G.IsRegularOfDegree D)
    (hlam : IsLeast (spectrum ℝ (G.adjMatrix ℝ)) lam)
    (S : Finset V) :
    (D : ℝ) / (2 * (Fintype.card V : ℝ)) * (S.card : ℝ) ^ 2 +
        lam / (2 * (Fintype.card V : ℝ)) * (S.card : ℝ) *
          ((Fintype.card V : ℝ) - (S.card : ℝ)) ≤
      (#(G.induce (S : Set V)).edgeFinset : ℝ) := by
  classical
  cases isEmpty_or_nonempty V with
  | inl _ =>
      simp
  | inr _ =>
      let χ : V → ℝ := fun v ↦ if v ∈ S then 1 else 0
      let one : V → ℝ := fun _ ↦ 1
      let N : ℝ := Fintype.card V
      let s : ℝ := S.card
      let c : ℝ := s / N
      let x : V → ℝ := χ - c • one
      have hN : 0 < N := by
        have hNnat : 0 < Fintype.card V :=
          Fintype.card_pos_iff.mpr (inferInstance : Nonempty V)
        dsimp [N]
        exact_mod_cast hNnat
      have hNne : N ≠ 0 := ne_of_gt hN
      have hχsum : dotProduct χ one = s := by
        simp [dotProduct, χ, one, s]
      have hχχ : dotProduct χ χ = s := by
        simp [dotProduct, χ, s]
      have honeone : dotProduct one one = N := by
        simp [dotProduct, one, N]
      have hAone : Matrix.mulVec (G.adjMatrix ℝ) one = (D : ℝ) • one := by
        funext v
        simpa [one] using
          (G.adjMatrix_mulVec_const_apply_of_regular (α := ℝ) hreg (a := (1 : ℝ)) (v := v))
      have hχAχ :
          dotProduct χ (Matrix.mulVec (G.adjMatrix ℝ) χ) =
            (2 * #(G.induce (S : Set V)).edgeFinset : ℝ) :=
        indicator_dotProduct_adjMatrix_indicator G S
      have hχAone :
          dotProduct χ (Matrix.mulVec (G.adjMatrix ℝ) one) = (D : ℝ) * s := by
        rw [hAone]
        simp [dotProduct_smul, hχsum]
      have honeAχ :
          dotProduct one (Matrix.mulVec (G.adjMatrix ℝ) χ) = (D : ℝ) * s := by
        calc
          dotProduct one (Matrix.mulVec (G.adjMatrix ℝ) χ) =
              dotProduct one (Matrix.mulVec (Matrix.transpose (G.adjMatrix ℝ)) χ) := by
                rw [G.transpose_adjMatrix]
          _ = dotProduct χ (Matrix.mulVec (G.adjMatrix ℝ) one) :=
            Matrix.dotProduct_transpose_mulVec _ _ _
          _ = (D : ℝ) * s := hχAone
      have honeAone :
          dotProduct one (Matrix.mulVec (G.adjMatrix ℝ) one) = (D : ℝ) * N := by
        rw [hAone]
        simp [dotProduct_smul, honeone]
      have hxx : dotProduct x x = s - s ^ 2 / N := by
        dsimp [x, c]
        rw [sub_dotProduct, dotProduct_sub, dotProduct_sub]
        simp only [smul_dotProduct, dotProduct_smul, hχχ, hχsum, dotProduct_comm one χ,
          honeone, smul_eq_mul]
        field_simp
        ring
      have hxAx :
          dotProduct x (Matrix.mulVec (G.adjMatrix ℝ) x) =
            (2 * #(G.induce (S : Set V)).edgeFinset : ℝ) - (D : ℝ) * s ^ 2 / N := by
        dsimp [x, c]
        rw [Matrix.mulVec_sub, Matrix.mulVec_smul, sub_dotProduct, dotProduct_sub,
          dotProduct_sub]
        simp only [smul_dotProduct, dotProduct_smul, hχAχ, hχAone, honeAχ, honeAone,
          smul_eq_mul]
        field_simp
        ring
      have hHerm : (G.adjMatrix ℝ).IsHermitian := by
        rw [Matrix.isHermitian_iff_isSymm]
        exact G.transpose_adjMatrix
      have hspectral := min_spectrum_mul_dotProduct_le_of_isHermitian hHerm hlam x
      rw [hxx, hxAx] at hspectral
      dsimp [N, s] at hspectral ⊢
      have hcardne : (Fintype.card V : ℝ) ≠ 0 := by
        have hnpos : 0 < Fintype.card V :=
          Fintype.card_pos_iff.mpr (inferInstance : Nonempty V)
        exact_mod_cast hnpos.ne'
      field_simp [hcardne] at hspectral ⊢
      nlinarith

end SimpleGraph

namespace SimpleGraph.KneserCounting

/-- The Kneser graph is regular of degree `choose (n - k) k`. -/
theorem isRegularOfDegree_graph (n : ℕ) {k : ℕ} (hk : 0 < k) :
    (graph n k).IsRegularOfDegree (regularDegree n k) := by
  classical
  intro A
  let valEmbedding : Vertex n k ↪ Finset (Fin n) :=
    ⟨fun B ↦ (B : Finset (Fin n)), fun _ _ h ↦ Subtype.ext h⟩
  have hmap :
      ((graph n k).neighborFinset A).map valEmbedding =
        ((A : Finset (Fin n))ᶜ).powersetCard k := by
    ext B
    simp only [Finset.mem_map, SimpleGraph.mem_neighborFinset, Finset.mem_powersetCard]
    constructor
    · rintro ⟨B', hB'A, rfl⟩
      have hdisjoint := (graph_adj_iff_disjoint n k hk).mp hB'A
      refine ⟨?_, Set.powersetCard.card_eq B'⟩
      intro x hxB
      exact Finset.mem_compl.mpr fun hxA ↦
        Finset.disjoint_left.mp hdisjoint hxA hxB
    · rintro ⟨hBA, hBcard⟩
      let B' : Vertex n k := ⟨B, hBcard⟩
      refine ⟨B', (graph_adj_iff_disjoint n k hk).mpr ?_, rfl⟩
      exact Finset.disjoint_left.mpr fun x hxA hxB ↦
        (Finset.mem_compl.mp (hBA hxB)) hxA
  calc
    (graph n k).degree A = #((graph n k).neighborFinset A) := rfl
    _ = #(((graph n k).neighborFinset A).map valEmbedding) := (Finset.card_map _).symm
    _ = #(((A : Finset (Fin n))ᶜ).powersetCard k) := by rw [hmap]
    _ = ((n - k).choose k) := by
      rw [Finset.card_powersetCard, Finset.card_compl, Fintype.card_fin,
        Set.powersetCard.card_eq A]
    _ = regularDegree n k := rfl

/-- The local-density coefficient in Proposition 2.7. -/
noncomputable def densityParameter (ε : ℝ) (n k : ℕ) : ℝ :=
  (ε / (1 + ε)) *
    ((regularDegree n k : ℝ) * (n : ℝ) /
      ((vertexCount n k : ℝ) * ((n - k : ℕ) : ℝ)))

/-- **Proposition 2.7 (proved from Theorems 2.5 and 2.6).**

Every sufficiently large vertex set in the Kneser graph spans a positive proportion of all its
possible edges.
-/
theorem kneser_supersaturation_of_isLeast
    {ε : ℝ} {n k : ℕ}
    (hε : 0 < ε) (hk : 0 < k) (hnk : 2 * k + 1 ≤ n)
    (hmin : IsLeast (spectrum ℝ ((graph n k).adjMatrix ℝ))
      (-((k : ℝ) / (((n - k : ℕ) : ℝ)) * (regularDegree n k : ℝ))))
    (S : Finset (Vertex n k))
    (hS : (1 + ε) * (starSize n k : ℝ) ≤ (S.card : ℝ)) :
    densityParameter ε n k * (S.card.choose 2 : ℝ) ≤
      (#((graph n k).induce (S : Set (Vertex n k))).edgeFinset : ℝ) := by
  classical
  let N : ℝ := vertexCount n k
  let D : ℝ := regularDegree n k
  let M : ℝ := starSize n k
  let s : ℝ := S.card
  let d : ℝ := ((n - k : ℕ) : ℝ)
  have hnpos : 0 < n := by omega
  have hkle : k ≤ n := by omega
  have hdNat : 0 < n - k := by omega
  have hNnat : 0 < vertexCount n k := by
    exact Nat.choose_pos hkle
  have hN : 0 < N := by
    dsimp [N]
    exact_mod_cast hNnat
  have hD : 0 ≤ D := by positivity
  have hs : 0 ≤ s := by positivity
  have hd : 0 < d := by
    dsimp [d]
    exact_mod_cast hdNat
  have hdiff : d + (k : ℝ) = (n : ℝ) := by
    dsimp [d]
    exact_mod_cast Nat.sub_add_cancel hkle
  have he : 0 < 1 + ε := by linarith
  have hstarNat :
      n * starSize n k = k * vertexCount n k := by
    simpa [starSize, vertexCount, Nat.sub_add_cancel hnpos,
      Nat.sub_add_cancel hk, mul_comm] using Nat.add_one_mul_choose_eq (n - 1) (k - 1)
  have hstar : (n : ℝ) * M = (k : ℝ) * N := by
    dsimp [M, N]
    exact_mod_cast hstarNat
  have hmixed :=
    SimpleGraph.expander_mixing_induced_edge_count (graph n k)
      (isRegularOfDegree_graph n hk) hmin S
  rw [card_vertex] at hmixed
  change
    D / (2 * N) * s ^ 2 +
        (-((k : ℝ) / d * D)) / (2 * N) * s * (N - s) ≤
      (#((graph n k).induce (S : Set (Vertex n k))).edgeFinset : ℝ) at hmixed
  have hchoose : (S.card.choose 2 : ℝ) ≤ s ^ 2 / 2 := by
    rw [Nat.cast_choose_two]
    have hsub : ((S.card - 1 : ℕ) : ℝ) ≤ s := by
      dsimp [s]
      exact_mod_cast Nat.sub_le S.card 1
    nlinarith [mul_le_mul_of_nonneg_left hsub hs]
  have hdensity : 0 ≤ densityParameter ε n k := by
    rw [densityParameter]
    positivity
  calc
    densityParameter ε n k * (S.card.choose 2 : ℝ) ≤
        densityParameter ε n k * (s ^ 2 / 2) :=
      mul_le_mul_of_nonneg_left hchoose hdensity
    _ ≤ D / (2 * N) * s ^ 2 +
        (-((k : ℝ) / d * D)) / (2 * N) * s * (N - s) := by
      have hid :
          (D / (2 * N) * s ^ 2 +
              (-((k : ℝ) / d * D)) / (2 * N) * s * (N - s)) -
              densityParameter ε n k * (s ^ 2 / 2) =
            D * s * (n : ℝ) / (2 * N * d * (1 + ε)) *
              (s - (1 + ε) * M) := by
        rw [densityParameter]
        dsimp [D, N, M, d]
        field_simp
        dsimp [N, M] at hstar
        dsimp [d] at hdiff
        linear_combination
          (D * s * (1 + ε)) * hstar +
          (D * s ^ 2 * (1 + ε)) * hdiff
      have hfactor :
          0 ≤ D * s * (n : ℝ) / (2 * N * d * (1 + ε)) := by positivity
      have hthreshold : 0 ≤ s - (1 + ε) * M := by
        dsimp [s, M]
        exact sub_nonneg.mpr hS
      nlinarith [mul_nonneg hfactor hthreshold]
    _ ≤ (#((graph n k).induce (S : Set (Vertex n k))).edgeFinset : ℝ) := hmixed

/-- **Proposition 2.7.**
Every sufficiently large vertex set in the Kneser graph spans
a positive proportion of all possible edges.
-/
theorem kneser_supersaturation
    {ε : ℝ} {n k : ℕ}
    (hε : 0 < ε)
    (hk : 0 < k)
    (hnk : 2 * k + 1 ≤ n)
    (S : Finset (Vertex n k))
    (hS :
      (1 + ε) * (starSize n k : ℝ) ≤ (S.card : ℝ)) :
    densityParameter ε n k * (S.card.choose 2 : ℝ) ≤
      (#((graph n k).induce
        (S : Set (Vertex n k))).edgeFinset : ℝ) := by
  exact kneser_supersaturation_of_isLeast
    hε hk hnk
    (kneser_least_eigenvalue
      (n := n) (k := k) hk hnk)
    S hS

end SimpleGraph.KneserCounting
