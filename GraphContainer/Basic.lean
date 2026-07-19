/-
Copyright (c) 2026 Graph Container formalization team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Graph Container formalization team
-/
module

public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum
public import Mathlib.Data.Finset.Powerset

/-!
# Graph containers: basic definitions

This file contains the public predicates and small data structures used by the graph container
argument.  The formal statement uses finite vertex types, so the number `N` in the paper is
`Fintype.card V`.

The paper omits the necessary hypothesis `q ≤ N`.  It is included in `Hypotheses`: without it,
`N.choose q = 0`, so no family of that cardinality can cover even the empty independent set.
-/

@[expose] public section

open Finset

namespace SimpleGraph.Container

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The number of edges spanned by a finite set of vertices. -/
def inducedEdgeCount (A : Finset V) : ℕ :=
  #(G.induce (A : Set V)).edgeFinset

/-- `G` is locally `β`-dense above threshold `R` if every vertex set of size at least `R`
spans at least `β * (|A| choose 2)` edges. -/
def IsLocallyDense (β : ℝ) (R : ℕ) : Prop :=
  ∀ A : Finset V, R ≤ #A →
    β * (A.card.choose 2 : ℝ) ≤ (inducedEdgeCount G A : ℝ)

/-- The hypotheses of the graph container theorem.

The exponential inequality is the stopping condition from Theorem 2.1.  The `q_le_card` field is
the correction to the printed statement discussed above. -/
structure Hypotheses (β : ℝ) (R q : ℕ) : Prop where
  beta_pos : 0 < β
  beta_lt_one : β < 1
  q_le_card : q ≤ Fintype.card V
  locallyDense : IsLocallyDense G β R
  shrink : Real.exp (-β * (q : ℝ)) * (Fintype.card V : ℝ) ≤ (R : ℝ)

/-- A family of sets is an `(R, q)` graph-container family if all its members have size at most
`R + q` and every independent set is contained in a member. -/
def IsContainerFamily (R q : ℕ) (𝒞 : Finset (Finset V)) : Prop :=
  (∀ C ∈ 𝒞, #C ≤ R + q) ∧
    ∀ I : Finset V, G.IsIndepSet I → ∃ C ∈ 𝒞, I ⊆ C

/-- The state of the Kleitman-Winston algorithm. -/
structure State (V : Type*) where
  /-- Vertices selected for the fingerprint. -/
  selected : Finset V
  /-- Vertices that remain active. -/
  active : Finset V

namespace State

/-- Initially no vertex is selected and every vertex is active. -/
def initial : State V where
  selected := ∅
  active := univ

end State

/-- All candidate fingerprints of cardinality `q`. -/
def fingerprints (q : ℕ) : Finset (Finset V) :=
  univ.powersetCard q

omit [DecidableEq V] in
@[simp] theorem mem_fingerprints {q : ℕ} {S : Finset V} :
    S ∈ fingerprints (V := V) q ↔ #S = q := by
      rw [fingerprints, mem_powersetCard]
      constructor
      · intro h
        exact h.2
      · intro h
        exact ⟨subset_univ S, h⟩

omit [DecidableEq V] in
@[simp] theorem card_fingerprints (q : ℕ) :
    #(fingerprints (V := V) q) = (Fintype.card V).choose q := by
      rw [fingerprints, card_powersetCard, card_univ]

end SimpleGraph.Container
