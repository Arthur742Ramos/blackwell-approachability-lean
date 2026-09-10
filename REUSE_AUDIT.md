# Reuse audit

Audit date: 2026-09-10. Dependency snapshot: Mathlib revision
`db584cd6d46c92f209a44c0f1c829460d327499d`.

The selected development reuses stable Mathlib infrastructure for:

- finite coordinate sums (`Fin.sum_univ_succ`) and finite case analysis;
- vector and matrix multiplication (`Matrix.mulVec`, `dotProduct`);
- transpose transport for the dot product
  (`Matrix.dotProduct_transpose_mulVec`) and determinant-based injectivity
  (`Matrix.eq_zero_of_mulVec_eq_zero`);
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
the determinant consequence, the development formalizes the dimension-three
affine-hyperplane mechanism in the proof of the source's Lemma 4: an invertible
properizer transports a nonzero affine normal `w` to `Sᵀw`, a nonzero common
invariant, which the three skew maps cannot share. The transport proof is
generic in the action set and selected comparator index set, then specializes
to the cited simplex family. The local scope intentionally stops before the
source’s broader affine/rate/minimality theory and its derivation of the
canonical equation from general affine reduction data, rather than rephrasing
a narrower theorem as that broader result.

No external formalization is imported. The Challenge source is independently
Mathlib-only; the implementation exposes public helpers so the checked Solution
has no private-name dependency across the comparison boundary.
