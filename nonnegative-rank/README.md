# Finite nonnegative rank and latent product mixtures in Lean

This standalone Lean 4 development proves an exact finite-cardinality bridge
between two descriptions of a joint probability table. For every fixed
component count `k`, a probability matrix is a mixture of `k` product
distributions if and only if it admits a nonnegative factorization with inner
dimension `k`; moreover, a count is least on one side exactly when it is least
on the other. The normalization proof explicitly handles zero-mass factors,
so no positivity assumption is hidden in the equivalence.

It also proves a support-based lower bound: a family of positive cells with
pairwise incompatible cross-cells needs at least as many nonnegative
rank-one components as the family has members. The uniform diagonal table on
`Fin N` is the sharp example: it has an `N`-component product-mixture
representation, and every such representation has at least `N` components.

The development concerns exact finite probability tables and exact
factorizations. It does not implement a rank-computation algorithm, address
approximate factorization, or formalize general latent-variable models. The
mathematical results are established ones; the contribution is a self-contained
Lean formalization with explicit finite-index and zero-factor boundaries.

## Build and verify

```sh
lake update
lake exe cache get
lake build
bash scripts/verify-palomar.sh
```

`NonnegativeRankChallenge.lean` is Mathlib-only. `NonnegativeRankSolution.lean`
contains the proofs, and `NonnegativeRankExamples.lean` checks concrete small
instances. The pinned Comparator configuration selects the four statements
documented in `formalization.yaml`.
