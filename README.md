# Blackwell Approachability in Lean

This repository formalizes the deterministic Euclidean core of Blackwell
approachability and connects it to finite repeated games and a quantitative
regret reduction. It targets Lean 4.33.0 with a pinned Mathlib snapshot.

## Formalized results

For a nonempty closed convex target `C`, a running average `avg`, closest-point
witnesses `proj`, and bounded witness-relative payoffs, the main certificate is

```text
dist (avg T) C <= B / sqrt T
```

for every positive horizon `T`. The same recurrence is proved with a uniform
supporting-half-space error, yielding

```text
dist (avg T) C <= sqrt (B^2 / T + epsilon).
```

The strategic layer adds finite pure and mixed player actions, a pure opponent
sequence, and a response depending on the current average. Under the explicit
pointwise Blackwell response condition, it constructs a strategy and proves the
bound against every opponent sequence. A separate Sion theorem proves the
general compact-convex bridge from pointwise feasibility to one uniform
response under stated continuity and quasiconvexity assumptions.

The reduction layer represents finite-action average regrets as a Euclidean
vector. An `l2` certificate implies every coordinate regret bound, while the
reverse estimate costs `sqrt (card A)`; a constant vector proves that this
factor is attained.

## Proof architecture

- `BlackwellApproachability.lean` proves projection geometry, the exact and
  additive-error recurrences, quantitative telescoping, and response-oracle
  adapters.
- `BlackwellGame.lean` defines finite mixed actions and proves pure/mixed
  repeated-game strategy and convergence theorems.
- `BlackwellMinimax.lean` proves the reusable Sion minimax response bridge.
- `BlackwellReduction.lean` proves the approachability-to-regret norm
  conversions.
- `BlackwellChallenge.lean` is the independent Mathlib-only statement surface;
  `BlackwellSolution.lean` supplies the checked proof adapters.
- `BlackwellGameExamples.lean` and `BlackwellSubstantiveExamples.lean` are
  executable checked examples of the game and regret layers. The earlier
  `BlackwellExamples.lean` contains nonzero cancellation and response-oracle
  certificates.

## Exact scope

The finite-game theorems quantify over every pure opponent action sequence and
construct a Markov response, but the pointwise supporting-half-space response
condition is an explicit hypothesis. The Sion result is a general theorem; it
does not instantiate every finite simplex or prove a game-specific minimax
condition automatically. The development does not model stochastic sampling,
last-iterate guarantees, computational complexity, or a practical algorithm.
It makes no claim of mathematical priority for the standard Blackwell or
approachability/no-regret arguments.

## Build and verification

The dependency graph is pinned in `lake-manifest.json`.

```bash
lake build
bash scripts/verify-palomar.sh
```

The preparation gate checks the independent Challenge imports, the exact
eleven-declaration Challenge/Solution surface, absence of implementation
placeholders, source dependency closure, the named-theorem axiom allowlist,
metadata alignment, and all checked examples. The pinned Comparator/NanoDa
replay is available through `scripts/verify-comparator.sh`; on macOS it
requires the explicit `PALOMAR_ALLOW_UNSANDBOXED_LOCAL=1` fallback because
Landrun's kernel sandbox is Linux-only. Hosted verification uses real Landrun.

## Attribution

The motivating sources are David Blackwell's vector-payoff minimax theorem,
Maurice Sion's minimax theorem, and the approachability/no-regret connection
of Abernethy, Bartlett, and Hazan. The metadata and
`THIRD_PARTY_NOTICES.md` contain the references. AI assistance was used for
proof engineering. The final definitions, statements, and proofs are checked
by Lean.
