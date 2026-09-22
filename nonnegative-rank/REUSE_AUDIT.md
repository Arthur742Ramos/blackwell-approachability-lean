# Reuse audit

The project uses the pinned Mathlib revision
`db584cd6d46c92f209a44c0f1c829460d327499d` and its finite sums, real-order
lemmas, finite equivalences, and standard choice/typeclass infrastructure.
Searches of the pinned Mathlib source found stochastic-matrix APIs and
rank-one operator material, but no API for arbitrary rectangular nonnegative
factorizations, normalized product-mixture cardinalities, or fooling-set
lower bounds. The doubly-stochastic matrix API is not a substitute: it concerns
square matrices with prescribed row and column sums, rather than the inner
dimension of an arbitrary nonnegative factorization.

Accordingly, this package defines only the finite probability-matrix and
factorization predicates needed for its selected statements. It introduces no
external proof code and imports no other Palomar entry. The Challenge has a
Mathlib-only dependency closure. The normalization argument is local because
its zero-mass cases are part of the exact statement being formalized.

The mixture/factorization connection is discussed by Carlini and Rapallo for
probability matrices and contingency-table mixture models. The fooling-set
lower-bound method is standard in nonnegative-rank theory; this package proves
the finite support argument directly from factor nonnegativity.
