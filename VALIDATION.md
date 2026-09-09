# Validation record

The local validation gate is scripts/verify-palomar.sh.

It checks:

- a complete Lean build;
- exact Mathlib-only Challenge source dependencies;
- exactly two Challenge proof holes and no implementation placeholders;
- exact selected theorem names and permitted axioms;
- metadata and citation alignment;
- the running-average regression certificate and a nonzero cancellation
  certificate that starts outside its singleton target;
- clean source formatting.

The separate Comparator replay is pinned in scripts/verify-comparator.sh.
A hosted run is required before describing the package as Comparator-verified.
Palomar intake, editorial review, registration, and public indexing are
separate external states and are not inferred from a green local or hosted
build.
