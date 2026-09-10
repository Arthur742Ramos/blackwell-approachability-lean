# Validation record

The local validation gate is `scripts/verify-palomar.sh`.

It checks:

- a complete Lean build, including the irreducibility module and its concrete
  regression examples;
- an exact Mathlib-only Challenge dependency closure;
- exactly five Challenge proof holes and no implementation placeholders;
- the exact five selected theorem names and permitted axiom allowlist;
- that the Challenge/Solution each expose the valid-improper-instance,
  affine-hyperplane invariant transport, canonical-proper, and no-reduction
  predicates and declarations;
- that the documentation and metadata state the canonical normal form rather
  than overclaiming a broader reduction theorem;
- the official pinned Palomar renderer’s isolated core-notation audit;
- metadata and citation alignment; and
- clean source formatting.

The separate Comparator replay is pinned in `scripts/verify-comparator.sh`.
On macOS it requires `PALOMAR_ALLOW_UNSANDBOXED_LOCAL=1`; a hosted Linux run is
required before describing the artifact as Comparator-verified. Palomar intake,
editorial review, registration, and public indexing are separate external
states and are never inferred from a local build alone.
