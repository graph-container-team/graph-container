# Graph containers and intersecting families in Lean

This repository contains a complete Lean formalization of the graph container theorem from
Theorem 2.1 and its application to counting intersecting uniform families in Theorem 2.3. It is
designed as a collaborative precursor to a mathlib contribution.  The theorem-specific source
tree contains no `sorry`, `admit`, or axiomatized mathematical steps.

## Toolchain

- Lean `v4.32.0`
- mathlib `v4.32.0`

Build the complete framework with:

```bash
lake update
lake build GraphContainer
```

If GitHub access needs the local proxy configuration:

```bash
proxy-on
lake update
```

## Main declarations

- `SimpleGraph.graph_container_theorem`: the container-family conclusion of Theorem 2.1.
- `SimpleGraph.graph_container_card_indepSetFinset_le`: the bound on independent `m`-sets.
- `SimpleGraph.Container.fingerprint_certificate`: the stronger internal statement supporting the
  counting theorem.
- `SimpleGraph.Container.containerFamily`: a canonical family indexed by all `q`-subsets.
- `SimpleGraph.KneserCounting.intersectingFamilyCount`: the number of intersecting `k`-uniform families on
  `Fin n`.
- `SimpleGraph.KneserCounting.kneser_least_eigenvalue`: the least-eigenvalue formula for the
  Kneser graph.
- `SimpleGraph.KneserCounting.eventually_intersectingFamilyCount_lt`: the strict, uniform upper
  bound in Theorem 2.3.

The paper's notation `N` is represented by `Fintype.card V`.

## Necessary correction to the PDF

The formal theorem includes `q ≤ N`. Without this hypothesis, `N.choose q = 0` when `q > N`, but
the claimed family must still contain a container covering the empty independent set. Thus the
printed statement is false in that edge case.

The counting conclusion is proved through the stronger fingerprint-remainder certificate. It does
not follow merely from the two displayed properties of the container family.

For Theorem 2.3, the real expressions for `R` and `q` are rounded up to natural numbers, and the
star lower bound omitted from the displayed proof is included. The notation `o(1)` is interpreted
uniformly as `n -> infinity` while `k = k(n)` may vary subject to the eventual hypotheses.

## Layout

- `GraphContainer/Basic.lean`: density, hypotheses, family predicate, and algorithm state.
- `GraphContainer/MaxDegreeOrder.lean`: deterministic max-degree ordering.
- `GraphContainer/Algorithm.lean`: selection, deletion, iteration, invariants, and reconstruction.
- `GraphContainer/Shrink.lean`: degree averaging, local-density estimates, and exponential decay.
- `GraphContainer/Family.lean`: remainders, containers, coverage, and the public family theorem.
- `GraphContainer/Counting.lean`: fingerprint-remainder encoding and the counting corollary.
- `GraphContainer/Intersecting/Basic.lean`: Kneser vertices, intersecting-family count, and stars.
- `GraphContainer/Intersecting/Spectrum.lean`: the Kneser spectrum and least eigenvalue.
- `GraphContainer/Intersecting/Supersaturation.lean`: the spectral local-density estimate.
- `GraphContainer/Intersecting/Container.lean`: the explicit finite container bound.
- `GraphContainer/Intersecting/Asymptotics.lean`: logarithmic error estimates.
- `GraphContainer/Intersecting/Theorem.lean`: the final strict upper-bound theorem.
- `IMPLEMENTATION.md`: the original Theorem 2.1 work packages.
- `THEOREM_2_3_IMPLEMENTATION.md`: the five new work packages and their dependency contracts.

The development modules live under `GraphContainer` so this repository can depend on mathlib
without pretending to be part of it. `IMPLEMENTATION.md` records the intended upstream paths.
