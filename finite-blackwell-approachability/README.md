# Finite Blackwell approachability from mixed minimax feasibility

This is a self-contained Lean 4 formalization of a finite-action quantitative
Blackwell approachability theorem. It formalizes known results and makes no
claim of new mathematical priority. Its central step turns a pointwise mixed
action condition into one uniform response by applying Sion minimax to the
two finite probability simplexes. A bounded-payoff estimate then supplies the
displacement bound needed for the finite-time approachability rate.

## Main result

Let A, B, and I be nonempty finite types. The player and opponent have action
sets A and B, and payoffs are finite real coordinate vectors indexed by I.
Let C be a nonempty, closed, convex subset of that space. Suppose every pure stage
payoff g a b has norm at most G, every target point has norm at most R, and
the following condition holds at every state y: for each mixed opponent
action q, some mixed player action p has expected payoff in the supporting
half-space at the projection of y onto C.

The convenience alias `FiniteEuclideanSpace I := I → ℝ` names the vector
space; selected theorem signatures inline `I → ℝ` for renderer stability. Its
Euclidean structure is given explicitly by the coordinate dot product
`∑ i, x i * y i`, norm `sqrt (∑ i, x i ^ 2)`, and the induced distance.
The Solution proves these coincide with Mathlib's standard inner product,
norm, and distance under `PiLp.continuousLinearEquiv` with
`EuclideanSpace ℝ I`. This keeps the challenge signatures concrete and
renderer-stable while reusing Mathlib's projection theorem internally.

Then there is a causal map from the expected running payoff to a mixed player
action such that, for every pure opponent-action sequence and every T > 0,

~~~text
distance(expected average payoff after T rounds, C) ≤ (G + R) / sqrt(T).
~~~

The expectation is over the player's mixed action. The theorem does not claim
a pathwise bound for sampled realized payoffs, nor a high-probability bound.
The opponent quantification is exactly over pure sequences ℕ → B; no claim
is made here about an opponent reacting to the realized private random draw.

## Proof outline and reuse boundary

1. A nonempty closed convex target has a closest-point projection satisfying
   the normal-cone inequality; this is proved by transport to Mathlib's
   complete Euclidean space.
2. Finite probability simplexes are nonempty, compact, and convex. The scalar
   normal score is bilinear, so Mathlib's Sion theorem turns “for each q, a
   feasible p exists” into one p that works against every q.
3. Point-mass opponent actions give the required one-step response against
   every pure opponent action.
4. The payoff bound and target-radius bound imply that the response's
   displacement from the projection is at most G + R.
5. The squared-distance recurrence yields the stated 1 / sqrt(T) rate.

The generic finite-time rate certificate in ApproachabilityCore.lean is
included so this directory builds independently. It is a self-contained copy
of support already present in the parent repository's
BlackwellApproachability.lean; that overlap is disclosed and is not presented
as new mathematics. The package's contribution is a standalone formalization
boundary: explicit finite-coordinate statements, nonemptiness guards, and a
checked adapter from those statements to Mathlib's Euclidean projection,
Sion minimax, and rate results. This is a formalization and assembly of known
theory, not a priority claim. The package imports no other Lean development
beyond its pinned Mathlib dependency.

The mathematical setting follows
[Blackwell's vector-payoff approachability framework](https://msp.org/pjm/1956/6-1/pjm-v6-n1-p01-p.pdf).
The minimax step uses Mathlib's
[Sion.exists_isSaddlePointOn](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/Sion.html).
Sion's original minimax paper is [On general minimax theorems](https://doi.org/10.2140/pjm.1958.8.171).
Finite-time approachability rates are also studied by
[Perchet and Mannor (2013)](https://proceedings.mlr.press/v30/Perchet13.html).
This development is a formalization and quantitative assembly, not a claim
of mathematical priority for approachability or its rate.

## Build and audit

The Lean version and Mathlib revision are pinned by lean-toolchain,
lakefile.lean, and lake-manifest.json.

~~~sh
lake exe cache get
lake build
lake env lean FiniteBlackwellExamples.lean
bash scripts/verify-palomar.sh
~~~

On Linux, the pinned Comparator/NanoDa audit is:

~~~sh
bash scripts/verify-comparator.sh
~~~

That script builds pinned external verification tools and runs the configured
Challenge/Solution comparison; the hosted workflow runs it in a Linux
environment with Landrun. All four selected statements are mirrored in
FiniteBlackwellChallenge.lean and FiniteBlackwellSolution.lean. The Challenge
imports Mathlib only.

## Files

- FiniteBlackwell.lean — finite simplexes, projections, expected payoffs,
  and the Sion minimax response theorem.
- ApproachabilityCore.lean — the self-contained finite-time rate certificate
  used by the strategy proof.
- FiniteBlackwellRate.lean — response-to-rate theorem and the main result.
- FiniteBlackwellChallenge.lean / FiniteBlackwellSolution.lean — the
  independent Palomar proof surface and its checked solution.
- FiniteBlackwellExamples.lean — a fully checked matching-pennies instance.
- comparator.json / formalization.yaml — theorem selection and formalization
  scope metadata for this nested project only.
