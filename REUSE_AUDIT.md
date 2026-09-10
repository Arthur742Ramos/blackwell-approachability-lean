# Reuse audit

Audit date: 2026-09-10. Dependency snapshot: Mathlib revision
`db584cd6d46c92f209a44c0f1c829460d327499d`.

The selected development reuses stable Mathlib infrastructure for:

- finite coordinate sums and finite case analysis (`Fin.sum_univ_succ`,
  `fin_cases`);
- vector/matrix multiplication and dot products (`Matrix.mulVec`,
  `dotProduct`);
- transpose transport and determinant-based injectivity
  (`Matrix.dotProduct_transpose_mulVec`,
  `Matrix.eq_zero_of_mulVec_eq_zero`);
- the explicit three-by-three determinant expansion (`Matrix.det_fin_three`);
- real-arithmetic normalization and certified inequalities (`ring`,
  `linarith`, `nlinarith`, `norm_num`).

Searches over this pinned Mathlib checkout found no existing formalization of
phi-regret, improper phi-regret, either cited comparator family, the source's
canonical correction, or its finite-dimensional reduction obstructions. The
project therefore defines the small domain-specific predicates
`validImproperInstance`, `validImproperFamily`, `canonicalProper`,
`canonicalProperReduction`, `affineHyperplaneWitness`, `extremePoint`, and
`antipodalDisplacements` locally, while reusing Mathlib's general algebra.

The construction follows Dann et al., Section 4.4.1. For the skew family, the
fixed point and endpoint calculations were checked against the published
formula `phi_q = Id - M_q`. For the second family, the published matrices
`A`, `B`, and coefficient square were transcribed directly; the implementation
independently checks its homogeneous kernel identity, nonnegativity, and
positive normalizing mass rather than treating the source's computer-search
discovery as a proof oracle. The middle coordinate of the kernel is
`2(36a² - 41ab + 71b²)`, as determined by direct multiplication against the
transcribed matrices.

The canonical normal form is stated exactly as `p + S (phi(p) - p)`. The
development formalizes the dimension-three affine-hyperplane transport in the
proof of source Lemma 4 and the extreme-point antipodal mechanism in the proof
of source Lemma 5. Both are generic in the action set and selected comparator
index set. The local scope intentionally stops before the source's broader
affine/rate/minimality theory and its derivation of the canonical equation from
general affine reduction data, rather than rephrasing a narrower theorem as a
broader result.

No external formalization is imported. The Challenge source is independently
Mathlib-only; the implementation exposes public helpers so the checked Solution
has no private-name dependency across the comparison boundary.
