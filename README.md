# Irreducible Improper φ-Regret in Lean

This repository formalizes a concrete separation result from Dann, Mansour,
Mohri, Schneider, and Sivan, “Rate-Preserving Reductions for Blackwell
Approachability,” COLT 2025. It is a source-grounded formalization of a
nontrivial finite-dimensional obstruction, not a claim of new mathematics.

## Result

Let `Δ₃` be the three-action probability simplex. For a comparator coefficient
vector `q = (a,b,c) ∈ Δ₃`, define

```text
φq(p₁,p₂,p₃) =
  (p₁ - a p₂ + b p₃,
   p₂ + a p₁ - c p₃,
   p₃ - b p₁ + c p₂).
```

Equivalently, `φq = Id - Mq` for the skew-symmetric matrix

```text
        [ 0  a -b ]
Mq =    [ -a 0  c ] .
        [ b -c  0 ]
```

The checked result establishes all of the following.

- Every `φq` has the explicit fixed point `(c,b,a) ∈ Δ₃`.
- The family is genuinely improper: `φ(1,0,0)(0,1,0) = (-1,1,0)`, which lies
  outside `Δ₃`.
- For any action set `P` in real three-space contained in an affine hyperplane
  `⟨p,w⟩ = b`, an invertible canonical properizer transports the nonzero
  normal `w` to `Sᵀw`, a nonzero vector `v` satisfying
  `⟨φq(p) - p, v⟩ = 0` for every selected comparator and every `p ∈ P`.
  This is the affine-hyperplane core of the source’s Lemma 4. The skew family
  is a concrete simplex specialization.
- Three concrete endpoint calculations prove that this skew family has no
  nonzero common invariant vector.
- If a real `3 × 3` matrix `S` made every map
  `p ↦ p + S (φq(p) - p)` simplex-preserving, then `det S = 0`.
  Therefore no invertible `S` can produce a proper comparator family in this
  canonical normal form.

Together, the affine-normal transport, invariant-vector obstruction, and
determinant calculation give the key separation: the improper family cannot
be made proper through the single-invertible-matrix canonical normal form used
in the source’s linear-reduction analysis.

## Exact scope

The formalization targets the explicit construction in Section 4.4.1 of the
source and the dimension-three affine-hyperplane implication in the proof of
its Lemma 4. It assumes the paper’s canonical correction equation directly,
packages its affine-normal transport as a reusable lemma for arbitrary action
sets `P : Set (Fin 3 → ℝ)`, then specializes it to the source's skew family.
It does not formalize the paper’s wider affine-reduction machinery that derives
this normal form, its minimality and rate-preservation arguments, or an online
regret algorithm. That boundary is intentional: the five selected theorems
establish the concrete fixed-point, impropriety, affine-hyperplane transport,
skew-family obstruction, determinant, and no-reduction claims needed for this
finite construction.

The repository retains earlier Blackwell approachability, finite-game, minimax,
and norm-conversion modules as supporting work, but they are not the Palomar
selection.

## Layout

- `BlackwellIrreducibility.lean` contains the complete proof.
- `BlackwellChallenge.lean` is the Mathlib-only five-theorem statement
  surface.
- `BlackwellSolution.lean` provides checked adapters to the implementation.
- `BlackwellIrreducibilityExamples.lean` checks both the affine-hyperplane
  and simplex transport specializations, explicit endpoint calculations, and
  the headline predicates.
- `formalization.yaml` records the source-to-statement relationship and the
  exact scope.

## Build and verification

The dependency graph is pinned in `lake-manifest.json`.

```bash
lake build
bash scripts/verify-palomar.sh
```

The preparation gate checks the independent Challenge import closure, the exact
five-declaration Challenge/Solution surface, absence of implementation
placeholders, source dependency closure, named-theorem axiom allowlist, the
official renderer’s isolated notation audit, metadata alignment, and executable
construction regressions. The pinned Comparator/NanoDa replay is available via
`scripts/verify-comparator.sh`; macOS requires the explicit
`PALOMAR_ALLOW_UNSANDBOXED_LOCAL=1` fallback because Landrun’s kernel sandbox is
Linux-only. Hosted verification uses real Landrun.

## Attribution

The primary source is:

> Christoph Dann, Yishay Mansour, Mehryar Mohri, Jon Schneider, and
> Balasubramanian Sivan. “Rate-Preserving Reductions for Blackwell
> Approachability.” *Proceedings of the Thirty Eighth Conference on Learning
> Theory*, PMLR 291:1380–1414, 2025.

The formalization follows the source’s explicit construction and credits it
accordingly. AI assistance was used for proof engineering. The final
definitions, statements, and proofs are checked by Lean.
