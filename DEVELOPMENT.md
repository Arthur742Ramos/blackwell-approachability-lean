# Development notes

`BlackwellChallenge.lean` imports only Mathlib and contains exactly five proof
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

The selected central invariant argument is stated for an arbitrary action set
`P : Set Vec3` that has an affine-hyperplane witness `⟨p,w⟩ = b`, and for an
arbitrary selected comparator family on `P`. It transports the normal through
a hypothetical invertible correction matrix `S`. The resulting `Sᵀw` is
nonzero and satisfies

```text
⟨phi q p - p, Sᵀw⟩ = 0
```

for every selected comparator and every point of `P`. This is the
dimension-three affine-hyperplane core of the proof of Lemma 4 in the source,
under its displayed canonical correction equation. The source's skew family is
then a direct simplex specialization. Three endpoint tests force every
coordinate of any such common invariant to vanish, giving the source's first
irreducibility mechanism in this concrete family.

The earlier `columnSums S` transport lemma remains in the implementation as a
simplex-specific regression result. The selected surface instead exposes the
strictly more general affine-hyperplane statement. It does not hide the
source's unformalized derivation of the canonical correction equation from the
full bidirectional affine-equivalence definition.

The complementary determinant argument uses the same three endpoint tests. If
a candidate matrix `S` makes every corrected map

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
affine-hyperplane transport theorem's simplex specialization, the retained
simplex-specific transport lemma, the negative-coordinate impropriety witness,
endpoint calculations, the valid improper-instance theorem, the
no-common-invariant theorem, and the no-reduction corollary. The validation
gate also builds every default library and runs the official renderer notation
audit against exactly the five selected declarations.
