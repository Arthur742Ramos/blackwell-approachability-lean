# Reuse audit

The project was designed against Mathlib pinned at
`db584cd6d46c92f209a44c0f1c829460d327499d`.

- It reuses Mathlib finite sums, real order, subtypes, lists, `dotProduct`,
  `add_dotProduct`, and `dotProduct_neg`.
- It does not duplicate an existing Mathlib approachability, online-regret,
  or tensor-reduction theorem; the relevant application-level construction is
  represented directly in finite coordinates.
- It intentionally avoids importing the repository's earlier irreducibility
  project or supporting Blackwell experiments. The Challenge has a
  Mathlib-only dependency closure, and the nested project can be checked as a
  separate Palomar candidate.
- The central API uses Mathlib's standard `Nonempty` typeclass for both finite
  constraint and action index types. This rules out empty simplex and online
  strategy codomains without introducing a project-specific existence notion.

The source result is Theorem 4 of Dann et al. (COLT 2025), cited in
`formalization.yaml` and `CITATION.cff`. This project claims a finite
source-faithful specialization, not priority or novelty over that paper.
