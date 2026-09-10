# Validation record

The local validation gate is `scripts/verify-palomar.sh`.

It checks:

- a complete Lean build, including both explicit source-family certificates and
  their regression examples;
- an exact Mathlib-only Challenge dependency closure;
- exactly nine Challenge proof holes and no implementation placeholders;
- the exact nine selected theorem names and permitted axiom allowlist;
- that Challenge and Solution both expose the fixed-point/impropriety,
  affine-hyperplane, extreme-antipodal, invariant, and canonical-reduction
  predicates needed by the selected surface;
- that the documentation and metadata state the canonical normal form rather
  than overclaiming the broader source reduction theory;
- the official pinned Palomar renderer's isolated core-notation audit;
- metadata and citation alignment; and
- clean source formatting.

The separate Comparator replay is pinned in `scripts/verify-comparator.sh`.
On macOS it requires `PALOMAR_ALLOW_UNSANDBOXED_LOCAL=1`; a hosted Linux run is
required before describing the artifact as Comparator-verified. Palomar intake,
editorial review, registration, and public indexing are separate external
states and are never inferred from a local build alone.
