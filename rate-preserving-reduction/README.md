# Finite tight approachability-to-improper-regret reduction

Authors: Arthur Freitas Ramos, Ruy Jose Guerra Barretto de Queiroz, and David
Barros Hulak.

This is a self-contained Lean 4.33 / Mathlib formalization of a finite-simplex,
algorithmic specialization of Theorem 4 in Dann, Mansour, Mohri, Schneider,
and Sivan, “Rate-Preserving Reductions for Blackwell Approachability” (COLT
2025).

It is an independent nested Palomar project in the same repository as the
separately approved irreducibility artifact. Its submission root is this
directory, not the repository root, so it is intended to create a new Palomar
record rather than a version update of that earlier entry.

## Result

Let `m` and `n` be nonempty finite index types. Let the original action space
be the finite simplex `Delta_n`, and let the constraint family be the convex
hull `Delta_m` of `m` bilinear coordinate constraints. The construction uses
the joint simplex

```text
X = Delta_(m x n) = conv { w tensor p | w in Delta_m, p in Delta_n }.
```

The selected Lean statements make this tensor-hull model explicit. Each
coordinate vertex is proved to be the outer product of two point masses, and
`jointSimplex_eq_finiteTensorCombination` proves that a table is in the joint
simplex exactly when it is a finite convex combination of those vertices.
`outer_jointSimplex` proves that every outer product of mixed actions is also
in the joint simplex. Together, these statements identify the joint simplex
with the convex hull of the rank-one tensors in this finite model.

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
Its conclusion retains the supplied anchor, and gives both causal strategy maps
for that exact chosen anchor in `Delta_m`. The finite-trajectory headline has
the same anchor-preserving type. Both declarations explicitly require
`[Nonempty m]` and `[Nonempty n]`; the objective and improperness definitions
carry the same assumptions. In addition, both reduction predicates and the
improperness predicate include `Nonempty m ∧ Nonempty n` in their propositions,
so the exported claims carry explicit existence witnesses as well as the
typeclass guards. Neither the strategy quantifiers nor the comparator-escape
claim can be discharged through an empty mixed-action space.

## Selected statement map

The Comparator checks eleven declarations. The first group establishes the
finite tensor model; the remaining declarations formalize the exact reduction:

| Lean declaration | Mathematical content |
|---|---|
| `marginal_simplex` | Marginalizing any joint distribution gives a legal action distribution. |
| `outer_jointSimplex` | The outer product of two distributions is a legal joint action. |
| `elementaryTensor_eq_outer_pointMass` | Every coordinate vertex is a rank-one tensor of point masses. |
| `jointSimplex_eq_finiteTensorCombination` | Joint distributions are exactly finite convex combinations of coordinate vertices. |
| `marginal_outer` | Decoding the anchored lift recovers the original action. |
| `pairing_shift_sub_pairing_eq_score` | The one-step comparator-pairing difference equals the approachability score. |
| `regretSum_eq_approachSum` | Summing that identity gives equality over every finite horizon. |
| `regretLoss_eq_approachLoss` | The corresponding supremum objectives agree for each fixed trajectory and loss sequence. |
| `shift_is_improper` | The shifted comparator is outside the joint simplex, with nonempty index witnesses. |
| `finiteTensorTightReduction_of_anchor` | Explicit trajectory maps give exact loss preservation for each supplied anchor. |
| `algorithmicFiniteTensorTightReduction_of_anchor` | Causal history-dependent strategy maps give the same exact preservation. |

For the hull identity, the forward decomposition uses each table entry
`x(i,j)` as its coefficient; conversely, nonnegative coefficients summing to
one produce a nonnegative table of mass one. The vertex lemma identifies each
coordinate table with the outer product of the corresponding point masses.
For the reduction, marginalization supplies the decoder; bilinearity gives the
one-step pairing identity; finite summation and the pointwise identity give
objective equality; and the two strategy translations reuse the same loss
histories, so their trajectory equalities yield the headline reductions. The
improperness proof is separate and uses total mass: the shift adds a mass-one
outer product to a mass-one joint action.

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
unproved maximizer-selection principle is used by the reduction proof. The
constraint and action index types are explicitly nonempty, so this supremum
and the translated strategy spaces do not rely on empty-type totalization.

## Files

- `RateReduction.lean` — implementation and proofs.
- `RateReductionChallenge.lean` — Mathlib-only statement surface with eleven
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
