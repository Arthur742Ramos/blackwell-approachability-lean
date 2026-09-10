# Development notes

`BlackwellChallenge.lean` imports only Mathlib and contains exactly fifteen proof
placeholders, one per selected source-backed declaration.
`BlackwellSolution.lean` imports `BlackwellIrreducibility.lean`, contains no
placeholders, and mirrors the public declarations definitionally. The
Challenge deliberately owns local definitions so its surface can render
without implementation dependencies.

## First family: affine-normal transport

For `q=(a,b,c) ∈ Δ₃`, `skewPhi q` is `Id - Mq`, where `Mq` is the
odd-dimensional skew-symmetric matrix in the cited construction. Its fixed
point is `![c,b,a]`. The source's canonical correction is

```text
p ↦ p + S (phi q p - p).
```

The selected Lemma-4 core is stated for an arbitrary action set
`P : Set Vec3` with a nonzero affine normal `w` satisfying `⟨p,w⟩ = b` on
`P`, and an arbitrary selected comparator family. If an invertible `S` maps
every corrected comparator back into `P`, then `Sᵀw` is nonzero and satisfies

```text
⟨phi q p - p, Sᵀw⟩ = 0.
```

The skew family then has no nonzero common invariant: three endpoint tests
force all coordinates to zero. A complementary direct determinant proof tests
three corrected endpoints, forces all column sums of `S` to vanish, and proves
`det S = 0`.

## Second family: certified fixed points and antipodal obstruction

The second Section 4.4.1 family has

```text
phi(a,b)(p) = p + a A p + b B p,     (a,b) ∈ [-1,1]²,
```

for the two published three-by-three matrices. The implementation does not
trust a computer-search witness. It proves directly that

```text
k = (81a² - 46ab + 72b²,
     2(36a² - 41ab + 71b²),
     2(5a² + 8ab + 21b²))
```

is a right-kernel vector of `aA+bB`, that its entries are nonnegative, and
that its mass `163a² - 112ab + 256b²` is strictly positive unless `(a,b)=0`.
Thus `k / mass` is a simplex fixed point in the nonzero case; the zero case
uses `vertex0`. The individual positivity proofs use explicit
square-completion identities and `nlinarith` only as a certificate checker.

The generic Lemma-5 core says that, at an extreme action, two nonzero
antipodal displacements cannot both be canonically properized by an invertible
matrix. Its proof forms the unique positive convex combination of the two
corrected actions that returns to the extreme point, then uses matrix
injectivity to contradict the nonzero displacement. For the second family,
the first simplex vertex and coefficient endpoints `(1,0)`, `(-1,0)` give
the required antipodal pair. The all-ones vector is also proved to be a common
invariant of this family, which distinguishes the Lemma-5 route from the
affine-normal route.

## Equation-(16) normalized-reduction bridge

The source introduces `M_phi = Id - phi` and, after its minimality,
full-span, and affine-normalization steps, obtains

```text
M_psi = S M_phi,              (16)
psi(p) = p + S(phi(p) - p).  (17)
```

The development represents the first identity by
`normalizedMIntertwining` for a fixed comparator correspondence, a candidate
proper target family `psi`, and one matrix `S`. It proves the pointwise
Equation-(17) equality and converts properness of `psi` into
`canonicalProperOn`. Thus the two concrete no-go corollaries exclude every
invertible `normalizedProperReductionOn`, not just a correction equation
introduced as an unexplained assumption.

## Equation-(15) loss-basis bridge

The source obtains Equation (16) from the normalized pairing identity

```text
<M_phi p, S^T ell'> = <M_psi p, ell'>.  (15)
```

using the fact that the action and target-loss spaces have full span. The
selected `loss_basis_pairing_implies_normalized_matrix_identity` gives the
concrete `ℝ³` core of that step. It evaluates the pairing at the three standard
simplex vertices and against the columns of any matrix `B` with nonzero
determinant. For each action basis vector, the three pairings say that the
transpose of `B` annihilates the difference `N e_j - S M e_j`; determinant
injectivity makes the difference zero. The three resulting column equalities
give `N = S M`.

`lossBasisProperReductionOn` packages this finite source-normalized
certificate with a proper matrix target. The two new concrete corollaries use
the matrix representations of the skew and A/B families to rule it out. This
still does not derive Equation (15), the loss basis, or the normalized setup
from the source's full bidirectional affine-equivalence/rate machinery.

## Scope and regression policy

The development proves a finite loss-basis form of the source's Equation
(15)-to-(16) step and the algebraic implication from Equation (16) to its
canonical normal form (17). It does not claim the source's preceding
derivation of Equation (15), the required action/loss span witnesses, or its
general bidirectional affine-equivalence and rate/minimality theory, nor an
online algorithm. That boundary is deliberate and is checked in the
documentation and metadata gate.

The older approachability, game, minimax, and norm-conversion files remain
independent supporting experiments and are not selected by Comparator.
`BlackwellIrreducibilityExamples.lean` exercises both family certificates,
both generic obstructions, the Equation-(15)-to-(16) and
Equation-(16)-to-(17) bridges, and both classes of no-reduction corollaries.
The validation gate runs the official renderer notation audit and an axiom
audit over exactly the fifteen selected declarations.
