# Theorem 2.3 implementation plan

## 1. Scope

The sole mathematical target of this phase is Theorem 2.3 from `container-result.pdf`. We do not
add standalone formalizations of Theorems 2.5, 2.6, or Proposition 2.7. The Kneser calculation they
support is encapsulated by the single internal interface
`SimpleGraph.Kneser.isLocallyDense`.

The public endpoint is:

```lean
theorem SimpleGraph.Kneser.intersectingFamilyCount_log_ratio_tendsto_one
    (k : ℕ → ℕ)
    (hk : ∀ᶠ n in atTop, 3 ≤ k n ∧ 2 * k n + 1 ≤ n) :
    Tendsto
      (fun n ↦
        Real.log (intersectingFamilyCount n (k n) : ℝ) /
          (((n - 1).choose (k n - 1) : ℝ) * Real.log 2))
      atTop (𝓝 1)
```

Thus `o(1)` is uniform over every admissible sequence `k = k(n)`. Constant sequences recover the
fixed-`k` interpretation.

## 2. Finite model

`SimpleGraph.Kneser.Vertex n k` is the subtype of `k`-subsets of `Fin n`. The graph relation is
disjointness together with inequality, which keeps the definition loopless even outside the
eventual range of the theorem.

`intersectingFamilyCount n k` is the cardinality of the finset of all intersecting families of
these vertices. It includes the empty family. For positive `k`, these families are exactly the
independent sets of `SimpleGraph.Kneser.graph n k`.

Write:

```text
N = n.choose k
M = (n - 1).choose (k - 1)
D = (n - k).choose k
```

The parameter choices are:

```text
epsilon(n) = 1 / sqrt(n)
beta       = epsilon / (1 + epsilon) * D * n / (N * (n - k))
R          = ceil((1 + epsilon) * M)
q          = ceil(beta⁻¹ * log(N / R))
```

The finite proof establishes:

```text
2^M <= intersectingFamilyCount n k
    <= N.choose q * 2^(R + q).
```

The lower bound comes from all subfamilies of one full star. The upper bound is the existing graph
container theorem followed by counting all subsets of each container.

## 3. Necessary formal details

### Integral parameters

The PDF writes real expressions for `R` and `q`, although Theorem 2.1 requires natural numbers.
The framework uses natural ceilings. The `threshold_error_isLittleO` and
`fingerprintSize_isLittleO` interfaces explicitly account for these roundings.

### The `q <= N` condition

The corrected graph container theorem requires `q ≤ N`. This is carried by
`AdmissibleContainerParameters.fingerprint_le` and proved eventually for the concrete parameter
choice.

### The omitted lower bound

The last line of the PDF proves an upper bound. To obtain an asymptotic equality, the framework
also records the standard star lower bound in
`pow_starSize_le_intersectingFamilyCount`.

### Total definitions

All definitions make sense for every pair `(n, k)`. Positivity and nonzero-denominator facts are
needed only eventually, where they follow from `3 ≤ k` and `2 * k + 1 ≤ n`.

## 4. Dependency graph

```text
Intersecting/Basic
        |
        v
Intersecting/LocalDensity  ---- GraphContainer/Basic
        |
        v
Intersecting/ContainerBound ---- GraphContainer/Family
        |
        v
Intersecting/Parameters
        |
        v
Intersecting/Asymptotics
        |
        v
Intersecting/Theorem
```

The files expose stable interfaces so the five owners can work independently. Coordinate any
change to a declaration used by a later file before merging it.

## 5. Five work packages

### Person 1: finite Kneser encoding and the star lower bound

Owned file:

- `GraphContainer/Intersecting/Basic.lean`

Proof obligations:

1. Count `Vertex n k` by `n.choose k`.
2. Remove the redundant inequality from adjacency when `0 < k`.
3. Relate the subtype predicate to `Set.Intersecting`.
4. Relate intersecting families to Kneser independent sets.
5. Prove positivity of `intersectingFamilyCount` using the empty family.
6. Count a full star and prove that all its subfamilies are intersecting.
7. Derive the lower bound `2 ^ M ≤ intersectingFamilyCount n k`.

Acceptance command:

```bash
lake build GraphContainer.Intersecting.Basic
```

### Person 2: local density and rounded stopping time

Owned file:

- `GraphContainer/Intersecting/LocalDensity.lean`

Proof obligations:

1. Count the neighbors of a Kneser vertex and prove `D`-regularity.
2. Establish `isLocallyDense`, encapsulating precisely the Kneser calculation required by
   Theorem 2.3.
3. Prove positivity and the strict upper bound for `densityParameter`.
4. Use the ceiling definition of `fingerprintSize` to prove the exponential shrink inequality.

The spectral argument may use private helper lemmas inside this file, but it must not add separate
public targets for the other numbered results in the PDF.

Acceptance command:

```bash
lake build GraphContainer.Intersecting.LocalDensity
```

### Person 3: finite container counting

Owned file:

- `GraphContainer/Intersecting/ContainerBound.lean`

Proof obligations:

1. Count all independent sets covered by the canonical container family.
2. Transfer that bound to intersecting Kneser families.
3. Assemble `Container.Hypotheses` from `AdmissibleContainerParameters`.
4. Prove the directly usable finite upper bound.

Acceptance command:

```bash
lake build GraphContainer.Intersecting.ContainerBound
```

### Person 4: uniform parameter asymptotics

Owned file:

- `GraphContainer/Intersecting/Parameters.lean`

Proof obligations:

1. Prove that the full-star size tends to infinity uniformly in admissible `k`.
2. Prove `asymptoticEpsilon n -> 0`.
3. Verify all rounded parameters eventually satisfy `AdmissibleContainerParameters`.
4. Show the threshold rounding error is `o(M)`.
5. Show the fingerprint size is `o(M)` uniformly across the full range.

Acceptance command:

```bash
lake build GraphContainer.Intersecting.Parameters
```

### Person 5: logarithmic estimates and integration

Owned files:

- `GraphContainer/Intersecting/Asymptotics.lean`
- `GraphContainer/Intersecting/Theorem.lean`
- theorem-specific documentation and final integration

Proof obligations:

1. Bound `log₂ (N.choose q)` by a quantity that is `o(M)`.
2. Combine the three error terms and prove `containerOverhead -> 0`.
3. Convert the star lower bound into `1 ≤ normalizedLogCount` eventually.
4. Convert the finite container bound into the matching eventual upper bound.
5. Preserve the final squeeze proof in `Theorem.lean` and run all integration checks.

Acceptance command:

```bash
lake build GraphContainer.Intersecting.Theorem
```

## 6. Integration checklist

1. Each owner removes every `sorry` from the owned files.
2. Run the five acceptance commands above.
3. Confirm the theorem-specific tree contains no proof holes:

   ```bash
   rg -n '^\s*sorry\s*$' GraphContainer/Intersecting
   ```

4. Build the umbrella target:

   ```bash
   lake build GraphContainer
   ```

5. Run mathlib linters before upstreaming.
6. Replace the placeholder author line with the five contributor names.
7. Preserve the module order shown above when moving the files under a future mathlib namespace.
