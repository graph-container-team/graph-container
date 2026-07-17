/-
Copyright (c) 2026 Graph Container formalization team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Graph Container formalization team
-/
module

public import GraphContainer.Shrink

/-!
# Fingerprint reconstruction and the container family

The canonical family is indexed by all `q`-subsets of the vertex set.  For an independent
fingerprint `S`, its remainder is the active set obtained by replaying the algorithm on `S`.
For a non-independent `S`, the remainder is empty.  This convention lets the same family cover
independent sets smaller than `q`: extend such a set to an arbitrary `q`-set.

This is work package 4 in `IMPLEMENTATION.md`.
-/

@[expose] public section

open Finset

namespace SimpleGraph.Container

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- A certificate used by the stronger, counting-oriented form of the theorem. -/
structure IsCertificate (q R : ℕ) (I S A : Finset V) : Prop where
  fingerprint_subset : S ⊆ I
  fingerprint_card : #S = q
  remainder_card : #A ≤ R
  residual_subset : I \ S ⊆ A
  disjoint : Disjoint S A

/-- The active remainder reconstructed from a candidate fingerprint. -/
noncomputable def remainder (q : ℕ) (S : Finset V) : Finset V :=
  if G.IsIndepSet S ∧ #S = q then activeAfter G q S else ∅

/-- The container indexed by `S`. -/
noncomputable def container (q : ℕ) (S : Finset V) : Finset V :=
  S ∪ remainder G q S

/-- The canonical family, indexed by all `q`-element fingerprints. -/
noncomputable def containerFamily (q : ℕ) : Finset (Finset V) :=
  (fingerprints (V := V) q).image (container G q)

theorem subset_container (q : ℕ) (S : Finset V) :
    S ⊆ container G q S := by
  sorry

theorem remainder_eq_activeAfter {q : ℕ} {S : Finset V}
    (hS : G.IsIndepSet S) (hSq : #S = q) :
    remainder G q S = activeAfter G q S := by
  sorry

theorem remainder_eq_empty_of_not_certificate {q : ℕ} {S : Finset V}
    (hS : ¬(G.IsIndepSet S ∧ #S = q)) :
    remainder G q S = ∅ := by
  sorry

/-- Every valid fingerprint reconstructs a remainder of size at most `R`. -/
theorem card_remainder_le {β : ℝ} {R q : ℕ} (h : Hypotheses G β R q)
    {S : Finset V} (hS : G.IsIndepSet S) (hSq : #S = q) :
    #(remainder G q S) ≤ R := by
  sorry

/-- Every canonical container has the size bound claimed in Theorem 2.1. -/
theorem card_container_le {β : ℝ} {R q : ℕ} (h : Hypotheses G β R q)
    {S : Finset V} (hSf : S ∈ fingerprints (V := V) q) :
    #(container G q S) ≤ R + q := by
  sorry

theorem mem_containerFamily_iff {q : ℕ} {C : Finset V} :
    C ∈ containerFamily G q ↔
      ∃ S ∈ fingerprints (V := V) q, container G q S = C := by
  sorry

/-- The number of canonical containers is at most the number of `q`-fingerprints. -/
theorem card_containerFamily_le (q : ℕ) :
    #(containerFamily G q) ≤ (Fintype.card V).choose q := by
  sorry

omit [DecidableEq V] in
/-- A finset of size at most `q` extends to a `q`-fingerprint when `q ≤ |V|`. -/
theorem exists_fingerprint_superset {q : ℕ} (hqV : q ≤ Fintype.card V)
    {I : Finset V} (hIq : #I ≤ q) :
    ∃ S ∈ fingerprints (V := V) q, I ⊆ S := by
  sorry

/-- Strong form for independent sets of size at least `q`.  It exposes the fingerprint and the
small remainder needed by the fixed-cardinality counting corollary. -/
theorem fingerprint_certificate {β : ℝ} {R q : ℕ} (h : Hypotheses G β R q)
    {I : Finset V} (hI : G.IsIndepSet I) (hqI : q ≤ #I) :
    IsCertificate q R I (fingerprint G q I) (remainder G q (fingerprint G q I)) := by
  sorry

/-- A large independent set lies in the container indexed by its algorithmic fingerprint. -/
theorem subset_container_fingerprint {β : ℝ} {R q : ℕ} (h : Hypotheses G β R q)
    {I : Finset V} (hI : G.IsIndepSet I) (hqI : q ≤ #I) :
    I ⊆ container G q (fingerprint G q I) := by
  sorry

/-- Every independent set, including one with fewer than `q` vertices, lies in the canonical
family. -/
theorem exists_mem_containerFamily_of_isIndepSet {β : ℝ} {R q : ℕ}
    (h : Hypotheses G β R q) {I : Finset V} (hI : G.IsIndepSet I) :
    ∃ C ∈ containerFamily G q, I ⊆ C := by
  sorry

theorem isContainerFamily_containerFamily {β : ℝ} {R q : ℕ}
    (h : Hypotheses G β R q) :
    IsContainerFamily G R q (containerFamily G q) := by
  sorry

omit [DecidableEq V] in
/-- Bundled form of the graph container theorem. -/
theorem exists_container_family {β : ℝ} {R q : ℕ} (h : Hypotheses G β R q) :
    ∃ 𝒞 : Finset (Finset V),
      #𝒞 ≤ (Fintype.card V).choose q ∧ IsContainerFamily G R q 𝒞 := by
  sorry

end SimpleGraph.Container

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

omit [DecidableEq V] in
/-- **Graph container theorem** (Theorem 2.1 in the source PDF).

The hypothesis `q ≤ Fintype.card V` repairs the missing edge case in the printed statement. -/
theorem graph_container_theorem {β : ℝ} {R q : ℕ}
    (hβ_pos : 0 < β) (hβ_one : β < 1)
    (hqV : q ≤ Fintype.card V)
    (hdense : Container.IsLocallyDense G β R)
    (hshrink : Real.exp (-β * (q : ℝ)) * (Fintype.card V : ℝ) ≤ (R : ℝ)) :
    ∃ 𝒞 : Finset (Finset V),
      #𝒞 ≤ (Fintype.card V).choose q ∧
        (∀ C ∈ 𝒞, #C ≤ R + q) ∧
          ∀ I : Finset V, G.IsIndepSet I → ∃ C ∈ 𝒞, I ⊆ C := by
  sorry

end SimpleGraph
