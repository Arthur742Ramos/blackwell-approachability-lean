# Development notes

`BlackwellChallenge.lean` imports only Mathlib and contains exactly three proof
placeholders, one for each selected source-backed theorem.
`BlackwellSolution.lean` imports `BlackwellIrreducibility.lean`, contains no
placeholders, and mirrors the public declarations definitionally. The Challenge
uses its own local names so it remains independently renderable.

The formalized action set is

```text
Δ₃ = { p : Fin 3 → ℝ | pᵢ ≥ 0 and Σᵢ pᵢ = 1 }.
```

For `q=(a,b,c) ∈ Δ₃`, `skewPhi q` is the map `Id - Mq`, where `Mq` is the
odd-dimensional skew-symmetric matrix from the cited construction. Its fixed
point is `![c,b,a]`. The proof establishes this algebraically, then transfers
simplex membership by permuting the coordinates of `q`.

The central determinant argument uses only three endpoint tests. If a candidate
matrix `S` makes every corrected map

```text
p ↦ p + S (skewPhi q p - p)
```

simplex-preserving, testing `(q,p)` at `(e₀,e₁)`, `(e₀,e₀)`, and `(e₁,e₀)`
forces the sums of columns `0`, `1`, and `2` of `S` to vanish. Rewriting the
three-by-three determinant with the resulting third-row equations proves
`det S = 0`.

This is the canonical normal form of the source’s reduction analysis. The
implementation deliberately does not fold in the larger theory that derives
that form from general affine reduction data, nor does it formalize learning
rates. That avoids overstating a finite matrix obstruction as a proof of every
broader reduction theorem in the paper.

The older approachability, game, minimax, and norm-conversion files remain in
the repository as independent supporting experiments. They are deliberately not
selected by the current Challenge or Comparator surface.

`BlackwellIrreducibilityExamples.lean` gives fast regression coverage for the
negative-coordinate impropriety witness, an endpoint calculation, the valid
improper-instance theorem, and the no-reduction corollary. The validation gate
also builds every default library and runs the official renderer notation audit
against exactly the three selected declarations.
