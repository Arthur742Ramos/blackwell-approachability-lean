# Validation record

The local validation gate is scripts/verify-palomar.sh.

It checks:

- a complete Lean build;
- exact Mathlib-only Challenge source dependencies;
- exactly eleven Challenge proof holes and no implementation placeholders;
- exact selected theorem names and permitted axioms;
- the official pinned Palomar renderer's isolated core-notation audit;
- metadata and citation alignment;
- the nonvacuity contract requiring `[Nonempty B]` on both selected repeated-game
  guarantees and the qualified scope of the dimension-factor sharpness claim;
- the running-average regression certificate, a nonzero cancellation
  certificate that starts outside its singleton target, the response-oracle
  certificate, a finite mixed-action game certificate, a pure-action game
  certificate, and the approachability-to-regret examples;
- clean source formatting.

The separate Comparator replay is pinned in scripts/verify-comparator.sh.
A hosted run is required before describing the package as Comparator-verified.
Palomar intake, editorial review, registration, and public indexing are
separate external states and are not inferred from a green local or hosted
build.
