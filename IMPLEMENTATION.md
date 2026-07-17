# Implementation plan

## 1. Formal target

Let `G : SimpleGraph V` with `V` finite, let `R q : ℕ`, and let `β : ℝ`. Assume:

1. `0 < β` and `β < 1`;
2. `q ≤ Fintype.card V`;
3. every `A : Finset V` with `R ≤ A.card` satisfies
   `β * (A.card.choose 2) ≤ inducedEdgeCount G A` after coercion to `ℝ`;
4. `exp (-β * q) * Fintype.card V ≤ R` after coercion to `ℝ`.

The public theorem produces `𝒞 : Finset (Finset V)` such that:

- `𝒞.card ≤ (Fintype.card V).choose q`;
- every `C ∈ 𝒞` has `C.card ≤ R + q`;
- every finite independent set of `G` is contained in some `C ∈ 𝒞`.

For `q ≤ m`, the counting theorem states:

```text
(G.indepSetFinset m).card
  ≤ (Fintype.card V).choose q * R.choose (m - q).
```

## 2. Statement corrections and design choices

### The missing `q ≤ N` hypothesis

The PDF needs `q ≤ N`. If `q > N`, then `N.choose q = 0`, while a family covering the empty
independent set cannot be empty. The Lean predicate `Hypotheses` therefore contains `q_le_card`.

### Why there is a stronger internal theorem

The size and coverage properties of an arbitrary container family yield at best a bound involving
`(R + q).choose m`. The sharper expression in the PDF uses additional structure:

- a fingerprint `S ⊆ I` with `S.card = q`;
- a remainder `A(S)` with `A(S).card ≤ R`;
- `I \ S ⊆ A(S)`.

This is recorded by `IsCertificate` and produced by `fingerprint_certificate`.

### Small independent sets

The algorithm selects `q` vertices only when `q ≤ I.card`. To cover smaller independent sets while
retaining exactly `N.choose q` indices, extend `I` to a `q`-set `S`. Every canonical container
contains its index `S`. For non-independent indices, the reconstructed remainder is defined to be
empty.

### Deterministic tie-breaking

`maxDegreeVertex` uses `Classical.choose` on the finite set of maximum-degree vertices. This avoids
adding an artificial `LinearOrder V` assumption to the public theorem while ensuring the active set
is a function of the fingerprint alone.

## 3. Module dependency graph

```text
Basic
  |
  v
MaxDegreeOrder
  |
  v
Algorithm
  |
  v
Shrink
  |
  v
Family
  |
  v
Counting
```

The chain is intentional. All interfaces already compile with `sorry`, so each owner may work
concurrently against downstream declarations. Do not change another owner's public theorem types
without first coordinating the interface change.

## 4. Five work packages

### Person 1: foundations and max-degree ordering

Owned files:

- `GraphContainer/Basic.lean`
- `GraphContainer/MaxDegreeOrder.lean`

Proof obligations:

1. Prove the two `fingerprints` membership and cardinality lemmas.
2. Unfold `Finset.exists_max_image` to prove membership and maximality of `maxDegreeVertex`.
3. Relate `degreeWithin` to degree in `G.induce A` using `map_neighborFinset_induce`.
4. Prove termination properties, `Nodup`, `toFinset`, and length of `maxDegreeOrder`.
5. Prove the maximum-degree property for every suffix of the ordering.

Acceptance command:

```bash
lake build GraphContainer.MaxDegreeOrder
```

### Person 2: algorithm and reconstruction

Owned file:

- `GraphContainer/Algorithm.lean`

Proof obligations:

1. Prove the three `firstIn` and `beforeVertex` list lemmas.
2. Establish monotonicity of selected and active sets.
3. Prove that selected vertices lie in the target and remain disjoint from the active set.
4. Use independence to show unselected target vertices survive every deletion.
5. Prove progress and exact fingerprint cardinality.
6. Prove `run_fingerprint_eq_run` by induction on the iteration count.

The reconstruction lemma is the critical interface for Persons 4 and 5.

Acceptance command:

```bash
lake build GraphContainer.Algorithm
```

### Person 3: density and exponential shrinkage

Owned file:

- `GraphContainer/Shrink.lean`

Proof obligations:

1. Transfer `SimpleGraph.sum_degrees_eq_twice_card_edges` to `degreeWithin`.
2. Derive a maximum-degree lower bound from the local-density hypothesis.
3. Count the prefix, selected vertex, and remaining neighbors deleted in one step.
4. Prove contraction by `1 - β` and iterate it while the final active set exceeds `R`.
5. Prove `(1 - β)^q ≤ exp (-β q)` using `Real.one_sub_le_exp_neg`.
6. Combine geometric decay with `Hypotheses.shrink` to prove `card_activeAfter_le`.

Acceptance command:

```bash
lake build GraphContainer.Shrink
```

### Person 4: canonical family and coverage

Owned file:

- `GraphContainer/Family.lean`

Proof obligations:

1. Simplify `remainder` for valid and invalid fingerprints.
2. Use reconstruction and shrinkage to prove `card_remainder_le`.
3. Bound each container and the image family.
4. Extend small finsets to `q`-subsets of `univ`.
5. Construct `IsCertificate` for every sufficiently large independent set.
6. Prove coverage for large and small independent sets, then discharge
   `SimpleGraph.graph_container_theorem`.

Acceptance command:

```bash
lake build GraphContainer.Family
```

### Person 5: counting and integration

Owned files:

- `GraphContainer/Counting.lean`
- `GraphContainer.lean`
- project documentation and final upstream port

Proof obligations:

1. Prove that `encoding` is injective by reconstructing `I` as fingerprint union residual.
2. Prove the generic `card_family_le_choose_mul_choose` lemma by counting fibers over
   `univ.powersetCard q`.
3. Verify fingerprint and residual cardinalities for independent `m`-sets.
4. Apply the generic lemma to `G.indepSetFinset m`.
5. Run the final no-`sorry`, build, and linter checks.

Acceptance command:

```bash
lake build GraphContainer
```

## 5. Collaboration rules

- Keep each declaration's statement stable once another work package depends on it.
- If a statement must change, update all consumers in the same commit or coordinate the change
  before merging.
- Prefer proving helper lemmas inside the owning module rather than importing a later module.
- Keep imports narrow. Do not replace the listed imports with `import Mathlib`.
- Do not add decidability assumptions to public mathematical theorems merely to simplify proofs.
  Use `classical` locally when appropriate.
- A work package is complete only when its owned file contains no `sorry` and its acceptance command
  produces no warning other than warnings inherited from unfinished dependencies.

## 6. Final integration checklist

1. Confirm no proof holes remain:

   ```bash
   rg -n '^\s*sorry\s*$' GraphContainer.lean GraphContainer
   ```

2. Build the umbrella target:

   ```bash
   lake build GraphContainer
   ```

3. Run mathlib linters on the eventual upstream modules.
4. Replace the team placeholder in copyright headers with the five contributor names.
5. Port the files as follows:

   ```text
   GraphContainer/Basic.lean
     -> Mathlib/Combinatorics/SimpleGraph/Container/Basic.lean
   GraphContainer/MaxDegreeOrder.lean
     -> Mathlib/Combinatorics/SimpleGraph/Container/MaxDegreeOrder.lean
   GraphContainer/Algorithm.lean
     -> Mathlib/Combinatorics/SimpleGraph/Container/Algorithm.lean
   GraphContainer/Shrink.lean
     -> Mathlib/Combinatorics/SimpleGraph/Container/Shrink.lean
   GraphContainer/Family.lean
     -> Mathlib/Combinatorics/SimpleGraph/Container/Family.lean
   GraphContainer/Counting.lean
     -> Mathlib/Combinatorics/SimpleGraph/Container/Counting.lean
   ```

6. Change downstream `GraphContainer.*` imports to the new `Mathlib.*` module paths.
7. Add the new public modules to mathlib's import graph and run the repository-wide lint command.
