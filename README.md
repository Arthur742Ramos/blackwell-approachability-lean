# Blackwell Approachability in Lean

This repository formalizes the quantitative Euclidean core of Blackwell
approachability in Lean 4.33.0 and Mathlib.

The main theorem is the finite-time certificate

  dist(avg T, C) <= B / sqrt(T)

for every positive horizon T. The hypotheses expose the usual Blackwell
geometry directly:

- each proj t is a closest point of the closed convex target C to avg t;
- the next payoff x t lies in the supporting half-space determined by
  avg t - proj t; and
- the witness-relative displacement has norm at most B.

The development proves the one-step squared-distance recurrence, telescopes it
by induction, supplies the affine recurrence for running averages, and proves
existence of the required closest point for every nonempty closed convex target
in a complete real inner-product space. BlackwellExamples.lean contains a
checked concrete certificate over the real line.

## Selected proof surface

The independent Mathlib-only statement file is BlackwellChallenge.lean.
The checked adapters are in BlackwellSolution.lean. The selected declarations
are:

- Blackwell.Palomar.blackwell_approachability_bound
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
no-regret equivalence developed by Abernethy, Bartlett, Hazan, and Rakhlin.

The formalization uses only Mathlib and does not import an external game-theory
formalization. AI assistance was used for proof engineering. The final
definitions, statements, and proofs are checked by Lean.

