# Blackwell Approachability in Lean

This repository formalizes a quantitative Euclidean certificate used in
Blackwell approachability in Lean 4.33.0 and Mathlib.

The main theorem is the conditional finite-time certificate

  dist(avg T, C) <= B / sqrt(T)

for every positive horizon T. The theorem assumes the usual Blackwell
supporting-half-space condition directly:

- each proj t is a closest point of the closed convex target C to avg t;
- the next payoff x t lies in the supporting half-space determined by
  avg t - proj t; and
- the witness-relative displacement has norm at most B.

This is the geometric convergence step of the argument. It does not state the
full strategic-game quantifiers and does not construct a strategy that
produces payoffs satisfying the half-space condition. A separate theorem
proves the closest-point and normal-cone geometry for nonempty
closed convex targets in complete real inner-product spaces; a game-specific
formalization would still have to prove the required response condition.

The development proves the one-step squared-distance recurrence, telescopes it
by induction, supplies the affine recurrence for running averages, and proves
existence of the required closest point for every nonempty closed convex target
in a complete real inner-product space. BlackwellExamples.lean contains
checked concrete certificates over the real line, including a nonzero
two-step cancellation sequence.

The implementation also provides `responseAverage` and
`blackwell_response_bound`. These define the average generated online by an
explicit response function and recover the same rate when the response
function satisfies the supporting-half-space and bounded-displacement
conditions for every current average. The response condition remains an input;
the package does not identify a game-theoretic action rule that guarantees it.

## Selected proof surface

The independent Mathlib-only statement file is BlackwellChallenge.lean.
The checked adapters are in BlackwellSolution.lean. The selected declarations
are:

- Blackwell.Palomar.blackwell_approachability_bound
- Blackwell.Palomar.blackwell_response_bound
- Blackwell.Palomar.exists_projection

The implementation theorem and supporting lemmas are in
BlackwellApproachability.lean.

## Build and verification

The pinned dependency graph is recorded in lake-manifest.json.

    lake build
    bash scripts/verify-palomar.sh

The verification script checks the independent Challenge imports, exact
Challenge/Solution theorem surface, absence of proof placeholders outside the
Challenge, source dependency closure, the named-theorem axiom allowlist,
metadata alignment, and whitespace cleanliness. The pinned Comparator/NanoDa
replay is available through scripts/verify-comparator.sh; on macOS it
requires the explicit PALOMAR_ALLOW_UNSANDBOXED_LOCAL=1 fallback because
Landrun's kernel sandbox is Linux-only. Hosted verification uses real Landrun.

## Scope and attribution

This is a formalization of the standard Blackwell approachability argument,
not a claim of priority for the mathematical theorem. The motivating sources
are David Blackwell's vector-payoff minimax theorem and the approachability /
no-regret equivalence developed by Abernethy, Bartlett, and Hazan.

The formalization uses only Mathlib and does not import an external game-theory
formalization. It makes no claim of priority for the standard argument. AI
assistance was used for proof engineering. The final definitions, statements,
and proofs are checked by Lean.
