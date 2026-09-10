# Development notes

`BlackwellChallenge.lean` imports only Mathlib and contains exactly thirty proof
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

## Direct finite affine action/loss-transfer and two-direction equivalence bridge

`invertibleTransferProperReductionOn` records the homogeneous finite
coordinate-change part of the source reduction. Its affine extension,
`invertibleAffineTransferProperReductionOn`, additionally records action and
loss translations `a` and `t`. Both certificates contain a target comparator
`theta`, action matrices `A`, `Ainv`, loss matrices `T`, `Tinv`, their
two-sided inverse equations, properness on the transformed action image, and
the exact per-round regret identity on `P` and the source loss cube `[0,1]^3`.

The proof of
`invertible_affine_transfer_proper_reduction_implies_canonical_properization`
does not assume Equation (16). It conjugates the target comparator back to
`P`, evaluates the transfer equality at the zero loss to cancel `t`, uses the
three standard cube losses to recover the vector equality, and constructs
`S = Ainv * Tinv.transpose`. The inverse identities prove that `S` is
nonsingular and that the resulting correction is proper. The concrete skew
and A/B corollaries rule out this one-way finite affine transfer, hence also
any stronger reduction which supplies such a transfer.

`affineLinearEquivalenceToProperOn` also records the source's two directional
pairing identities after fixing the comparator correspondence. It introduces
target action/loss sets, requires them to be exactly the affine images under
the coordinate maps, and retains explicit inverse matrices for both maps. Its
reverse pairing identity produces `invertibleAffineTransferProperReductionOn`,
so `affine_linear_equivalence_implies_canonical_properization` is a checked
bridge from that two-direction source-style regime to a canonical properizer.
The selected skew and A/B corollaries therefore rule it out as well.

This is not a proof of the source's general reduction-to-bijection step:
minimality, arbitrary comparator bijections, arbitrary target dimensions, and
rate preservation remain outside the formalized boundary.

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
certificate with a proper matrix target. The two concrete corollaries use
the matrix representations of the skew and A/B families to rule it out. This
still does not derive Equation (15), the loss basis, or the normalized setup
from the source's full bidirectional affine-equivalence/rate machinery.

## Equation-(18) finite vertex/corner bridge

Section 4.4.2 reduces a canonical-properness test over a polytope to the
membership constraints

```text
p_j + S(phi_i(p_j) - p_j) ∈ P.  (18)
```

The selected `matrixProperOn_simplex3_iff_on_vertices` proves the complete
action-side statement for the concrete simplex: a linear matrix comparator
maps all of `Delta_3` into itself exactly when it maps each of its three
standard basis vertices into `Delta_3`. The selected
`canonicalProperOn_simplex3_iff_vertex_constraints` composes that fact with
the checked representation `M_phi = Id - phi`, making the source's
action-vertex constraints available for a canonical correction.

The two source examples additionally have finite comparator polytopes that
can be handled without an optimization oracle. For the skew family,
`M_q` is linear in `q ∈ Delta_3`, so the three comparator vertices and the
three action vertices give nine sufficient-and-necessary constraints. For the
A/B family, the coefficient square uses the explicit four nonnegative
bilinear weights

```text
(1-a)(1-b)/4, (1-a)(1+b)/4,
(1+a)(1-b)/4, (1+a)(1+b)/4,
```

which sum to one. This proves that its four coefficient corners and three
action vertices give exactly twelve constraints. The existing canonical
obstructions are then lifted to no-invertible-solution theorems for both
finite systems.

This is deliberately a concrete source-family specialization of Equation
(18). It does not formalize the paper's general polytope representation,
linear-program construction, cone-span procedure, randomized invertibility
test, or its earlier reduction hypotheses.

## Scope and regression policy

The development proves direct finite affine action/loss-transfer and
two-direction affine-equivalence implications for the canonical normal form,
a finite loss-basis form of the source's
Equation
(15)-to-(16) step, the algebraic implication from Equation (16) to (17), and
concrete Equation-(18) membership reductions for the two cited families. It
does not derive the source's general affine-reduction maps from minimality,
or formalize its rate and set-span theory, its general Section 4.4.2 randomized
algorithm, or an online algorithm. That boundary is deliberate and checked in
the documentation and metadata gate.

The older approachability, game, minimax, and norm-conversion files remain
independent supporting experiments and are not selected by Comparator.
`BlackwellIrreducibilityExamples.lean` exercises both family certificates,
both generic obstructions, the direct-transfer and two-direction-equivalence
bridges, the Equation-(15)-to-
(16) and Equation-(16)-to-(17) bridges, the Equation-(18) vertex/corner
equivalences, and all classes of no-reduction corollaries.
The validation gate runs the official renderer notation audit and an axiom
audit over exactly the thirty selected declarations.
