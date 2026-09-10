# Finite tight approachability-to-improper-regret reduction

This is a self-contained Lean 4.33 / Mathlib formalization of a finite-simplex,
algorithmic specialization of Theorem 4 in Dann, Mansour, Mohri, Schneider,
and Sivan, “Rate-Preserving Reductions for Blackwell Approachability” (COLT
2025).

It is an independent nested Palomar project in the same repository as the
separately approved irreducibility artifact. Its submission root is this
directory, not the repository root, so it is intended to create a new Palomar
record rather than a version update of that earlier entry.

## Result

Let the original action space be the finite simplex `Delta_n`, and let the
constraint family be the convex hull `Delta_m` of `m` bilinear coordinate
constraints. The construction uses the joint simplex

```text
X = Delta_(m x n) = conv { w tensor p | w in Delta_m, p in Delta_n }.
```

For a joint action `x`, its action marginal is

```text
decode(x)(j) = sum_i x(i,j).
```

For a mixed constraint `w`, the improper comparator is

```text
shift(w,x) = x + w tensor decode(x).
```

The formalization proves:

- `shift` leaves the joint simplex for every legal `w` and `x`: its total
  mass is two, so the target is genuinely improper;
- the one-step phi-regret increment for `shift` is exactly the original
  mixed constraint score;
- summing gives equality for every finite horizon and every loss sequence;
- anchoring an original strategy in the joint simplex and decoding any joint
  strategy are explicit functions of the same prior-loss history; and
- both strategy translations preserve the finite-horizon loss exactly.

The headline theorem is
`Blackwell.RateReduction.Palomar.algorithmicFiniteTensorTightReduction_of_anchor`.
It gives both causal strategy maps for every chosen anchor in `Delta_m`.

## Why use the joint simplex?

The paper writes `X = U tensor P`. A point in a convex hull of elementary
tensors can have more than one decomposition. In the finite-simplex case,
`Delta_(m x n)` has a canonical linear action marginal, so `shift` is defined
on every joint action without selecting a decomposition. The identity checked
by Lean is the source equation

```text
B(x,l) - B(shift(w,x),l) = u_w(decode(x),l),
```

with `reducedLoss` implementing the source linear loss map `M_B`.

## Scope

This is a source-faithful finite convex-hull/simplex specialization, not a
claim to have formalized every generality in the paper. In particular it does
not formalize arbitrary bounded convex sets or abstract tensor products,
randomized strategies, computational complexity, asymptotic infimum-defined
rates, or the paper's later linear-equivalence characterizations. It proves
the exact objective equality from which rate preservation follows in this
finite deterministic strategy model.

The loss objective is represented with a real supremum over mixed constraints.
The central pointwise and finite-horizon equalities are unconditional; no
unproved maximizer-selection principle is used by the reduction proof.

## Files

- `RateReduction.lean` — implementation and proofs.
- `RateReductionChallenge.lean` — Mathlib-only statement surface with nine
  intentional theorem holes.
- `RateReductionSolution.lean` — checked adapters to the implementation.
- `RateReductionExamples.lean` — a concrete two-constraint, two-action,
  one-loss-coordinate validation instance.
- `comparator.json` and `formalization.yaml` — the independent Palomar entry
  configuration and provenance metadata.

## Verify

```bash
cd rate-preserving-reduction
bash scripts/verify-palomar.sh
```

After a clean commit, create a reproducible nested-entry archive with:

```bash
bash scripts/package-archive.sh
```

The script archives only this project beneath the
`rate-preserving-reduction/` prefix and prints the source commit and SHA-256.

For a local pinned Comparator replay on macOS, set
`PALOMAR_ALLOW_UNSANDBOXED_LOCAL=1` and run
`bash scripts/verify-comparator.sh`. A Linux hosted replay remains the
authoritative sandboxed check.

The Palomar fields for a new record are:

```text
repository: Arthur742Ramos/blackwell-approachability-lean
project_path: rate-preserving-reduction
comparator_config_path: rate-preserving-reduction/comparator.json
formalization_metadata_path: rate-preserving-reduction/formalization.yaml
existing_id: [leave blank]
```

No Palomar intake, editorial review, or registration is implied merely by
the local checks in this directory.
