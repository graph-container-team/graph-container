# Graph container theorem in Lean

This repository is a compile-ready Lean framework for Theorem 2.1, the graph container theorem,
from the supplied PDF. It is designed as a collaborative precursor to a mathlib contribution.

The mathematical definitions and the Kleitman-Winston algorithm are implemented. The 58
nontrivial proof obligations are deliberately left as granular `sorry` blocks so that five people
can work against stable interfaces.

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

The paper's notation `N` is represented by `Fintype.card V`.

## Necessary correction to the PDF

The formal theorem includes `q ≤ N`. Without this hypothesis, `N.choose q = 0` when `q > N`, but
the claimed family must still contain a container covering the empty independent set. Thus the
printed statement is false in that edge case.

The counting conclusion is proved through the stronger fingerprint-remainder certificate. It does
not follow merely from the two displayed properties of the container family.

## Layout

- `GraphContainer/Basic.lean`: density, hypotheses, family predicate, and algorithm state.
- `GraphContainer/MaxDegreeOrder.lean`: deterministic max-degree ordering.
- `GraphContainer/Algorithm.lean`: selection, deletion, iteration, invariants, and reconstruction.
- `GraphContainer/Shrink.lean`: degree averaging, local-density estimates, and exponential decay.
- `GraphContainer/Family.lean`: remainders, containers, coverage, and the public family theorem.
- `GraphContainer/Counting.lean`: fingerprint-remainder encoding and the counting corollary.
- `IMPLEMENTATION.md`: ownership, dependency contracts, and completion criteria for five people.

The development modules live under `GraphContainer` so this repository can depend on mathlib
without pretending to be part of it. `IMPLEMENTATION.md` records the intended upstream paths.
