/-
Copyright (c) 2026 Graph Container formalization team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Graph Container formalization team
-/
module

public import GraphContainer.Shrink

/-!
# Fingerprints and the canonical container family

This file turns the output of the Kleitman--Winston algorithm into a finite
family of containers.

For a `q`-set `S`, define its remainder to be:

* `activeAfter G q S` if `S` is independent;
* the empty set otherwise.

Its container is then `S ∪ remainder G q S`.
-/

@[expose] public section

open Finset

namespace SimpleGraph.Container

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-! ## Constructing Containers -/

/-- The remainder reconstructed from a fingerprint `S`.

If `S` is independent, replay the algorithm from `S` and return the
remaining active set. If `S` is not independent, return the empty set.
-/
noncomputable def remainder (q : ℕ) (S : Finset V) : Finset V :=
  if G.IsIndepSet S then activeAfter G q S else ∅

/-- The container indexed by a fingerprint `S`. -/
noncomputable def container (q : ℕ) (S : Finset V) : Finset V :=
  S ∪ remainder G q S

/-- The whole container family. -/
noncomputable def containerFamily (q : ℕ) : Finset (Finset V) :=
  (fingerprints (V := V) q).image (container G q)

/-- A container of a fingerprint has at most `R + q` vertices. -/
private theorem card_container_le {β : ℝ} {R q : ℕ}
    (h : Hypotheses G β R q)
    {S : Finset V} (hSq : #S = q) :
    #(container G q S) ≤ R + q := by
  by_cases hS : G.IsIndepSet S
  · rw [container, remainder, if_pos hS]
    calc
      #(S ∪ activeAfter G q S)
          ≤ #S + #(activeAfter G q S) :=
        Finset.card_union_le _ _
      _ ≤ q + R :=
        Nat.add_le_add hSq.le
          (card_activeAfter_le G h hS hSq.ge)
      _ = R + q := Nat.add_comm _ _
  · rw [container, remainder, if_neg hS, Finset.union_empty, hSq]
    exact Nat.le_add_left q R

/-- The container family has at most `(Fintype.card V).choose q` members. -/
theorem card_containerFamily_le (q : ℕ) :
    #(containerFamily G q) ≤ (Fintype.card V).choose q := by
  calc
    #(containerFamily G q) ≤ #(fingerprints (V := V) q) := by
      rw [containerFamily]
      exact Finset.card_image_le
    _ = (Fintype.card V).choose q := card_fingerprints q

/-! ## Covering independent sets -/

/-- Every independent set is contained in a container indexed by a `q`-set. -/
private theorem independent_subset_some_container {q : ℕ}
    (hqV : q ≤ Fintype.card V)
    {I : Finset V} (hI : G.IsIndepSet I) :
    ∃ S ∈ fingerprints (V := V) q, I ⊆ container G q S := by
  by_cases hqI : q ≤ #I
  · refine ⟨fingerprint G q I, ?_, ?_⟩
    · exact mem_fingerprints.mpr
        (card_fingerprint_of_le_card G hI hqI)
    · rw [container, remainder,
        if_pos (fingerprint_isIndepSet G hI q)]
      change I ⊆ fingerprint G q I ∪
        (run G (fingerprint G q I) q).active
      rw [run_fingerprint_eq_run G hI hqI]
      calc
        I = fingerprint G q I ∪ (I \ fingerprint G q I) :=
          (fingerprint_union_sdiff G I q).symm
        _ ⊆ fingerprint G q I ∪ activeAfter G q I :=
          Finset.union_subset_union_right
            (sdiff_fingerprint_subset_activeAfter G hI q)
  · have hIq : #I ≤ q := Nat.le_of_not_ge hqI
    obtain ⟨S, hIS, hS_card⟩ :=
      Finset.exists_superset_card_eq hIq hqV
    refine ⟨S, mem_fingerprints.mpr hS_card, hIS.trans ?_⟩
    rw [container]
    exact Finset.subset_union_left

/-! ## The main theorem -/

/-- The container family satisfies the size and covering requirements. -/
theorem containerFamily_isContainerFamily {β : ℝ} {R q : ℕ}
    (h : Hypotheses G β R q) :
    IsContainerFamily G R q (containerFamily G q) := by
  constructor
  · intro C hC
    rw [containerFamily] at hC
    obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hC
    exact card_container_le G h (mem_fingerprints.mp hS)
  · intro I hI
    obtain ⟨S, hS, hIS⟩ :=
      independent_subset_some_container G h.q_le_card hI
    refine ⟨container G q S, ?_, hIS⟩
    rw [containerFamily]
    exact Finset.mem_image_of_mem (container G q) hS

omit [DecidableEq V] in
/-- There is a family of at most `(Fintype.card V).choose q` containers, each
of cardinality at most `R + q`, that covers every independent set of `G`. -/
theorem graph_container_theorem {β : ℝ} {R q : ℕ}
    (h : Hypotheses G β R q) :
    ∃ 𝒞 : Finset (Finset V),
      #𝒞 ≤ (Fintype.card V).choose q ∧
        IsContainerFamily G R q 𝒞 := by
  classical
  exact
    ⟨containerFamily G q,
      card_containerFamily_le G q,
      containerFamily_isContainerFamily G h⟩

/-! ## Remaining for counting -/

/-- Four conditions for the container `(S, A)`. -/
structure IsCertificate (q R : ℕ) (I S A : Finset V) : Prop where
  fingerprint_subset : S ⊆ I
  fingerprint_card : #S = q
  remainder_card : #A ≤ R
  residual_subset : I \ S ⊆ A

/-- For a sufficiently large independent set, its algorithmic fingerprint and
the remainder reconstructed from that fingerprint form a certificate. -/
theorem fingerprint_certificate {β : ℝ} {R q : ℕ}
    (h : Hypotheses G β R q)
    {I : Finset V} (hI : G.IsIndepSet I) (hqI : q ≤ #I) :
    IsCertificate q R I
      (fingerprint G q I)
      (remainder G q (fingerprint G q I)) := by
  have hfp_indep :
      G.IsIndepSet (fingerprint G q I) :=
    fingerprint_isIndepSet G hI q

  rw [remainder, if_pos hfp_indep]

  have hrun :
      run G (fingerprint G q I) q = run G I q :=
    run_fingerprint_eq_run G hI hqI

  refine
    { fingerprint_subset := fingerprint_subset G I q
      fingerprint_card := card_fingerprint_of_le_card G hI hqI
      remainder_card := ?_
      residual_subset := ?_ }

  · change #(run G (fingerprint G q I) q).active ≤ R
    rw [hrun]
    exact card_activeAfter_le G h hI hqI

  · change I \ fingerprint G q I ⊆
      (run G (fingerprint G q I) q).active
    rw [hrun]
    exact sdiff_fingerprint_subset_activeAfter G hI q

end SimpleGraph.Container