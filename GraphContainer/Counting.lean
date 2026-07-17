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
  sorry

/-- Generic fingerprint-remainder counting lemma.  This lemma is independent of graph theory and
is intended to be reusable in later hypergraph-container work. -/
theorem card_family_le_choose_mul_choose
    (𝒜 : Finset (Finset V)) (m q R : ℕ)
    (fp rem : Finset V → Finset V)
    (hcard : ∀ I ∈ 𝒜, #I = m)
    (hcertificate : ∀ I ∈ 𝒜, IsCertificate q R I (fp I) (rem (fp I))) :
    #𝒜 ≤ (Fintype.card V).choose q * R.choose (m - q) := by
  sorry

variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem encoding_fst_mem_fingerprints {I : Finset V} (hI : G.IsIndepSet I)
    {q : ℕ} (hqI : q ≤ #I) :
    (encoding G q I).1 ∈ fingerprints (V := V) q := by
  sorry

theorem card_encoding_snd {I : Finset V} {m q : ℕ}
    (hI : G.IsIndepSet I) (hIm : #I = m) (hqI : q ≤ #I) :
    #(encoding G q I).2 = m - q := by
  sorry

theorem encoding_snd_subset_remainder {β : ℝ} {R q : ℕ}
    (h : Hypotheses G β R q) {I : Finset V}
    (hI : G.IsIndepSet I) (hqI : q ≤ #I) :
    (encoding G q I).2 ⊆ remainder G q (encoding G q I).1 := by
  sorry

/-- Counting form of the graph container theorem. -/
theorem card_indepSetFinset_le {β : ℝ} {R q m : ℕ}
    (h : Hypotheses G β R q) (hqm : q ≤ m) :
    #(G.indepSetFinset m) ≤
      (Fintype.card V).choose q * R.choose (m - q) := by
  sorry

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
  sorry

end SimpleGraph
