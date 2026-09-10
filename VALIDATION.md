# Validation record

The local validation gate is `scripts/verify-palomar.sh`.

It checks:

- a complete Lean build, including both explicit source-family certificates and
  their regression examples;
- an exact Mathlib-only Challenge dependency closure;
- exactly twenty-seven Challenge proof holes and no implementation placeholders;
- the exact twenty-seven selected theorem names and permitted axiom allowlist;
- that Challenge and Solution both expose the fixed-point/impropriety,
  affine-hyperplane, extreme-antipodal, invariant, homogeneous and affine
  action/loss-transfer,
  canonical-reduction, finite-loss-basis, and Equation-(15)/(16)/(17)/(18)
  bridge predicates
  needed by the selected surface;
- that the documentation and metadata distinguish the proved direct finite
  affine-transfer-to-canonical, Equation-(15)-to-(16),
  Equation-(16)-to-(17), and concrete Equation-(18) vertex/corner bridges
  from the unformalized broader source reduction theory and generic randomized
  algorithm;
- the official pinned Palomar renderer's isolated core-notation audit;
- metadata and citation alignment; and
- clean source formatting.

The separate Comparator replay is pinned in `scripts/verify-comparator.sh`.
On macOS it requires `PALOMAR_ALLOW_UNSANDBOXED_LOCAL=1`; a hosted Linux run is
required before describing the artifact as Comparator-verified. Palomar intake,
editorial review, registration, and public indexing are separate external
states and are never inferred from a local build alone.
