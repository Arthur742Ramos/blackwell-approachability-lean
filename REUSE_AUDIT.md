# Reuse audit

Audit date: 2026-09-09. Dependency snapshot: Mathlib revision
db584cd6d46c92f209a44c0f1c829460d327499d.

The implementation reuses the following stable Mathlib results:

- norm_add_sq_real for the one-step inner-product expansion;
- exists_norm_eq_iInf_of_complete_convex for closest-point existence;
- norm_eq_iInf_iff_real_inner_le_zero for the supporting half-space
  characterization;
- Metric.infDist_eq_iInf and Metric.infDist_le_dist_of_mem for the
  metric conclusion;
- finite-sum and scalar-algebra lemmas for the running-average recurrence.

No external formalization is imported. The Challenge source is independently
Mathlib-only, and the selected statements do not depend on local abbreviations
or opaque game-theory definitions.

