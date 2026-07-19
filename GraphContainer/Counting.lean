/-
Copyright (c) 2026 Graph Container formalization team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Graph Container formalization team
-/
module

public import GraphContainer.Family

/-!
# Counting independent sets from graph containers

An independent `m`-set is encoded by its `q`-element fingerprint and its `(m - q)`-element
residual subset of a remainder of size at most `R`.  This gives the product bound in the final
sentence of Theorem 2.1.

This is work package 5 in `IMPLEMENTATION.md`.
-/

@[expose] public section

open scoped BigOperators
open Finset

namespace SimpleGraph.Container

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Encode a vertex set by its algorithmic fingerprint and residual part. -/
noncomputable def encoding (G : SimpleGraph V) [DecidableRel G.Adj]
    (q : ℕ) (I : Finset V) : Finset V × Finset V :=
  (fingerprint G q I, I \ fingerprint G q I)

/-- The encoding is injective because its two components have union equal to the original set. -/
theorem encoding_injective (G : SimpleGraph V) [DecidableRel G.Adj] (q : ℕ) :
    Function.Injective (encoding G q) := by
  intro I J hIJ
  have hfst : fingerprint G q I = fingerprint G q J := by
    simpa only [encoding] using congrArg Prod.fst hIJ
  have hsnd : I \ fingerprint G q I = J \ fingerprint G q J := by
    simpa only [encoding] using congrArg Prod.snd hIJ
  calc
    I = fingerprint G q I ∪ (I \ fingerprint G q I) :=
      (fingerprint_union_sdiff G I q).symm
    _ = fingerprint G q J ∪ (J \ fingerprint G q J) :=
      congrArg₂ (fun S T ↦ S ∪ T) hfst hsnd
    _ = J := fingerprint_union_sdiff G J q

/-- Generic fingerprint-remainder counting lemma.  This lemma is independent of graph theory and
is intended to be reusable in later hypergraph-container work. -/
theorem card_family_le_choose_mul_choose
    (𝒜 : Finset (Finset V)) (m q R : ℕ)
    (fp rem : Finset V → Finset V)
    (hcard : ∀ I ∈ 𝒜, #I = m)
    (hcertificate : ∀ I ∈ 𝒜, IsCertificate q R I (fp I) (rem (fp I))) :
    #𝒜 ≤ (Fintype.card V).choose q * R.choose (m - q) := by
  classical
  let realized := 𝒜.image fp
  have hrealized_subset : realized ⊆ fingerprints (V := V) q := by
    intro S hS
    obtain ⟨I, hI, rfl⟩ := Finset.mem_image.mp hS
    exact mem_fingerprints.mpr (hcertificate I hI).fingerprint_card
  have hrealized_card : #realized ≤ (Fintype.card V).choose q := by
    calc
      #realized ≤ #(fingerprints (V := V) q) := card_le_card hrealized_subset
      _ = (Fintype.card V).choose q := card_fingerprints q
  have hfiber : ∀ S ∈ realized,
      #{I ∈ 𝒜 | fp I = S} ≤ R.choose (m - q) := by
    intro S hS
    obtain ⟨I₀, hI₀, hfp₀⟩ := Finset.mem_image.mp hS
    have hremS : #(rem S) ≤ R := by
      rw [← hfp₀]
      exact (hcertificate I₀ hI₀).remainder_card
    calc
      #{I ∈ 𝒜 | fp I = S} ≤ #((rem S).powersetCard (m - q)) := by
        refine card_le_card_of_injOn (fun I ↦ I \ S) ?_ ?_
        · intro I hIfiber
          change I ∈ {I ∈ 𝒜 | fp I = S} at hIfiber
          rw [mem_filter] at hIfiber
          obtain ⟨hI, hfpI⟩ := hIfiber
          have hcert := hcertificate I hI
          change I \ S ∈ (rem S).powersetCard (m - q)
          rw [mem_powersetCard]
          constructor
          · simpa only [hfpI] using hcert.residual_subset
          · have hSI : S ⊆ I := by
              simpa only [hfpI] using hcert.fingerprint_subset
            rw [card_sdiff_of_subset hSI, hcard I hI]
            have hScard : #S = q := by
              simpa only [hfpI] using hcert.fingerprint_card
            rw [hScard]
        · intro I hIfiber J hJfiber hsdiff
          change I ∈ {I ∈ 𝒜 | fp I = S} at hIfiber
          change J ∈ {I ∈ 𝒜 | fp I = S} at hJfiber
          rw [mem_filter] at hIfiber hJfiber
          obtain ⟨hI, hfpI⟩ := hIfiber
          obtain ⟨hJ, hfpJ⟩ := hJfiber
          have hSI : S ⊆ I := by
            simpa only [hfpI] using (hcertificate I hI).fingerprint_subset
          have hSJ : S ⊆ J := by
            simpa only [hfpJ] using (hcertificate J hJ).fingerprint_subset
          calc
            I = S ∪ (I \ S) := (union_sdiff_of_subset hSI).symm
            _ = S ∪ (J \ S) := congrArg (fun T ↦ S ∪ T) (by simpa only using hsdiff)
            _ = J := union_sdiff_of_subset hSJ
      _ = (#(rem S)).choose (m - q) := card_powersetCard _ _
      _ ≤ R.choose (m - q) := Nat.choose_le_choose _ hremS
  calc
    #𝒜 = ∑ S ∈ realized, #{I ∈ 𝒜 | fp I = S} :=
      card_eq_sum_card_image fp 𝒜
    _ ≤ ∑ _S ∈ realized, R.choose (m - q) := by
      exact sum_le_sum fun S hS ↦ hfiber S hS
    _ = #realized * R.choose (m - q) := by simp
    _ ≤ (Fintype.card V).choose q * R.choose (m - q) :=
      Nat.mul_le_mul_right _ hrealized_card

variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem encoding_fst_mem_fingerprints {I : Finset V} (hI : G.IsIndepSet I)
    {q : ℕ} (hqI : q ≤ #I) :
    (encoding G q I).1 ∈ fingerprints (V := V) q := by
  rw [mem_fingerprints]
  simpa only [encoding] using card_fingerprint_of_le_card G hI hqI

theorem card_encoding_snd {I : Finset V} {m q : ℕ}
    (hI : G.IsIndepSet I) (hIm : #I = m) (hqI : q ≤ #I) :
    #(encoding G q I).2 = m - q := by
  change #(I \ fingerprint G q I) = m - q
  rw [card_sdiff_of_subset (fingerprint_subset G I q), hIm,
    card_fingerprint_of_le_card G hI hqI]

theorem encoding_snd_subset_remainder {β : ℝ} {R q : ℕ}
    (h : Hypotheses G β R q) {I : Finset V}
    (hI : G.IsIndepSet I) (hqI : q ≤ #I) :
    (encoding G q I).2 ⊆ remainder G q (encoding G q I).1 := by
  simpa only [encoding] using (fingerprint_certificate G h hI hqI).residual_subset

/-- Counting form of the graph container theorem. -/
theorem card_indepSetFinset_le {β : ℝ} {R q m : ℕ}
    (h : Hypotheses G β R q) (hqm : q ≤ m) :
    #(G.indepSetFinset m) ≤
      (Fintype.card V).choose q * R.choose (m - q) := by
  apply card_family_le_choose_mul_choose (fp := fingerprint G q) (rem := remainder G q)
  · intro I hI
    exact (mem_indepSetFinset_iff.mp hI).card_eq
  · intro I hI
    have hNI := mem_indepSetFinset_iff.mp hI
    apply fingerprint_certificate G h hNI.isIndepSet
    simpa only [hNI.card_eq] using hqm

end SimpleGraph.Container

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The fixed-cardinality counting conclusion of the graph container theorem. -/
theorem graph_container_card_indepSetFinset_le
    {β : ℝ} {R q m : ℕ}
    (hβ_pos : 0 < β) (hβ_one : β < 1)
    (hqV : q ≤ Fintype.card V)
    (hdense : Container.IsLocallyDense G β R)
    (hshrink : Real.exp (-β * (q : ℝ)) * (Fintype.card V : ℝ) ≤ (R : ℝ))
    (hqm : q ≤ m) :
    #(G.indepSetFinset m) ≤
      (Fintype.card V).choose q * R.choose (m - q) := by
  apply Container.card_indepSetFinset_le G
    ({ beta_pos := hβ_pos
       beta_lt_one := hβ_one
       q_le_card := hqV
       locallyDense := hdense
       shrink := hshrink } : Container.Hypotheses G β R q)
    hqm

end SimpleGraph
