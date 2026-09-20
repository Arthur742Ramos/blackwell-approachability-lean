# Reuse and scope audit

## Mathlib results reused

- Mathlib.Topology.Sion: Sion.exists_isSaddlePointOn supplies the saddle
  point for the scalar bilinear normal score on the two finite probability
  simplexes. The proof separately establishes nonemptiness, compactness,
  convexity, and continuity/quasiconvexity hypotheses.
- Mathlib.Analysis.InnerProductSpace.Projection.Minimal:
  exists_norm_eq_iInf_of_complete_convex and
  norm_eq_iInf_iff_real_inner_le_zero supply nearest-point existence and the
  normal-cone inequality for nonempty closed convex targets in complete real
  inner-product spaces.
- The finite `PiLp` inner-product and norm formulas, together with
  `PiLp.continuousLinearEquiv`, identify the public coordinate dot product,
  norm, and distance with Mathlib's standard Euclidean structures. These
  equivalences are proved in the Solution; `PiLp` does not appear in the
  selected theorem signatures.
- Finite sums, product topologies, and finite-dimensional continuity are
  supplied by the pinned Mathlib imports. No external Lean proof development
  is imported.

## Repository overlap

ApproachabilityCore.lean is included so a fresh checkout of this nested Lake
package does not depend on the repository root. It reproduces the generic
finite-time rate-certificate support already developed in
BlackwellApproachability.lean at parent-repository snapshot
42b9d7c77e77fc158d44cb31ef320798c3c73492. That overlap is disclosed in the
README and formalization metadata and is not presented as a new result. The
selected finite-action theorems are a coordinate-explicit standalone
formalization and adapter layer over the locally included projection,
finite-simplex minimax, and rate support. No underlying Blackwell or Sion
result, or the generic rate certificate, is claimed as new mathematics.

## Scope boundary

The selected result is finite-action, finite-dimensional, and
expectation-valued. The payoff type is the raw finite-coordinate function
space `FiniteEuclideanSpace I := I → ℝ`. Its public dot product, norm, and
distance are explicit finite-coordinate formulas. The Solution proves these
agree with Mathlib's Euclidean structures through
`PiLp.continuousLinearEquiv` before reusing the generic projection and rate
results. The selected declarations avoid exposing PiLp aliases to downstream
renderers. It does not prove a pathwise or high-probability guarantee for
sampled play, an adaptive-opponent protocol, or a general
topological-vector-space theorem, or an executable strategy. The source papers
are cited in the metadata and README; no proof text is copied from them.
