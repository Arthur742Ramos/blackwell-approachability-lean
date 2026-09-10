# Validation record

The main local gate is `scripts/verify-palomar.sh`. It checks:

- Mathlib-only source dependencies for `RateReductionChallenge.lean`;
- exactly nine intentional Challenge holes and no placeholder, `axiom`, or
  `unsafe` declaration in implementation, Solution, or examples;
- the exact Comparator declaration list and permitted-axiom allowlist;
- a complete Lake build plus the concrete two-by-two example;
- the pinned official Palomar renderer's isolated core-notation audit for all
  nine selected declarations;
- an axiom report for every selected declaration; and
- metadata, citation, and source-shape consistency.

`scripts/verify-comparator.sh` pins Comparator, Lean4Export, NanoDa, and
Landrun. On macOS it needs the explicit unsandboxed fallback opt-in; a Linux
hosted run is required before calling the result Comparator-verified.

After a clean commit, `scripts/package-archive.sh` creates a deterministic
entry-scoped ZIP, rejects generated and hidden members, and prints its
SHA-256. This archive and a hosted check are preparation evidence only.

Technical validation, Palomar mechanical verification, automated review,
editorial review, registration, and public indexing are separate states.
