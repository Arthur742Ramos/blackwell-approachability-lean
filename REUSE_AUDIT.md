# Reuse audit

Audit date: 2026-09-10. Dependency snapshot: Mathlib revision
`db584cd6d46c92f209a44c0f1c829460d327499d`.

The selected development reuses stable Mathlib infrastructure for:

- finite coordinate sums (`Fin.sum_univ_succ`) and finite case analysis;
- vector and matrix multiplication (`Matrix.mulVec`, `dotProduct`);
- the explicit three-by-three determinant expansion
  (`Matrix.det_fin_three`);
- real arithmetic normalization (`ring`, `linarith`, `norm_num`).

Searches over this pinned Mathlib checkout found linear-equivalence and matrix
infrastructure but no existing formalization of phi-regret, improper
phi-regret, the cited comparator family, or its reduction obstruction. The
project therefore defines the small domain-specific predicates
`validImproperInstance`, `canonicalProper`, `canonicalProperReduction`, and
the generic selected-family predicates locally, while reusing Mathlib’s general
algebra.

The construction follows Dann et al., Section 4.4.1. The fixed point and the
three endpoint calculations were checked against the published formulas: for
`q=(a,b,c)`, `M_q` is skew-symmetric and `(c,b,a)` is in its kernel. The
canonical normal form is stated exactly as `p + S (phi(p) - p)`. In addition to
the determinant consequence, the development formalizes the finite
common-invariant mechanism of the source's first obstruction: an invertible
properizer transports the simplex sum functional to a nonzero common invariant,
which the three skew maps cannot share. The transport proof is stated for an
arbitrary selected comparator family on the three-action simplex and is then
specialized to the cited family. The local scope intentionally stops before the
source’s broader affine/rate/minimality theory, rather than rephrasing a
narrower theorem as that broader result.

No external formalization is imported. The Challenge source is independently
Mathlib-only; the implementation exposes public helpers so the checked Solution
has no private-name dependency across the comparison boundary.
