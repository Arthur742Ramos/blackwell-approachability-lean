# Irreducible Improper φ-Regret in Lean

This repository formalizes two explicit three-action improper φ-regret
constructions from Section 4.4.1 of Dann, Mansour, Mohri, Schneider, and
Sivan, “Rate-Preserving Reductions for Blackwell Approachability,” COLT 2025.
It is a source-grounded formalization of the paper's finite-dimensional
obstructions, not a claim of new mathematics.

## Checked result

The public Challenge/Solution boundary selects fifteen declarations. Together,
they prove two distinct canonical-correction obstructions and connect them to
the source's normalized reduction identities.

### Skew-simplex family and the Lemma-4 mechanism

For `q = (a,b,c) ∈ Δ₃`, the first comparator is

```text
φq(p₁,p₂,p₃) =
  (p₁ - a p₂ + b p₃,
   p₂ + a p₁ - c p₃,
   p₃ - b p₁ + c p₂).
```

Every comparator has the explicit fixed point `(c,b,a) ∈ Δ₃`, while
`φ(1,0,0)(0,1,0) = (-1,1,0)` lies outside the simplex. The development proves:

- an invertible canonical properizer of any real three-dimensional action set
  contained in an affine hyperplane transports its normal `w` to a nonzero
  common invariant `Sᵀw`;
- the three skew comparators have no nonzero common invariant;
- direct endpoint calculations force every simplex-preserving correction
  matrix to have zero determinant; and
- consequently no invertible canonical correction makes the family proper.

The transport statement is the ambient-`ℝ³` canonical-correction core of the
source's Lemma 4.

### Matrix family and the Lemma-5 mechanism

The second construction has coefficient set `[-1,1]²` and maps

```text
φ(a,b)(p) = p + a A p + b B p,

    [ -6   8  -9 ]              [ 10  -3  -7 ]
A = [  2  -1  -9 ],       B = [  6  -6  10 ].
    [  4  -7  18 ]              [-16   9  -3 ]
```

For every `(a,b)`, Lean certifies a simplex fixed point. For nonzero
coefficients it normalizes the nonnegative kernel vector

```text
k(a,b) = (81a² - 46ab + 72b²,
          2(36a² - 41ab + 71b²),
          2(5a² + 8ab + 21b²))
```

by mass `163a² - 112ab + 256b²`; the zero-coefficient case uses a vertex.
The proof includes square-completion certificates for nonnegativity and strict
positive mass, so it does not rely on an external numerical solver. It also
shows that `(1,0)` is an improper comparator.

The second generic theorem formalizes the canonical-correction core of the
source's Lemma 5: if an extreme action has two selected comparators with
nonzero antipodal displacements, no invertible correction can map both back
into the action set. Instantiating it at the first simplex vertex and the
coefficient endpoints `(1,0)` and `(-1,0)` rules out a canonical properizer of
the matrix family. The all-ones vector is separately certified as a common
invariant of that family, explaining why the Lemma-4 mechanism alone does not
exclude it.

### Normalized reduction bridge

The paper's normalized reduction analysis writes `Mφ = Id - φ` and derives

```text
Mψ = S Mφ                                                    (16)
ψ(p) = p + S (φ(p) - p).                                     (17)
```

after fixing the comparator correspondence. This development now formalizes
that rearrangement: any proper target family `ψ` satisfying the global
Equation-(16) identity has the canonical properizer in Equation (17).
Consequently, both explicit families rule out an invertible *normalized
proper reduction*—an invertible `S`, a proper target family on the same
indexed comparators, and `Mψ = S Mφ`—not merely a separately postulated
canonical correction.

### Loss-pairing / dual-basis bridge

The preceding source step is the normalized loss-pairing identity

```text
⟨Mφ p, Sᵀℓ'⟩ = ⟨Mψ p, ℓ'⟩.                                  (15)
```

The new finite-dimensional theorem proves that testing (15) at the three
simplex vertices against any three linearly independent target losses already
forces `Mψ = S Mφ`. It does so by transporting the three pairings through the
transpose of the loss-basis matrix, using its nonzero determinant to separate
vectors, and then recovering the three matrix columns from the simplex basis.

This supports two further source-faithful corollaries: neither explicit family
admits an invertible proper *finite-loss-basis reduction* satisfying (15).
It formalizes the concrete dual-basis form of the paper’s full-span argument,
not just the later Equation-(16) rearrangement.

## Exact scope

The formalization proves the finite-dimensional Equation-(15)-to-(16) dual
basis argument, the algebraic Equation-(16)-to-(17) bridge, and the
consequences of the source's canonical normal form above. It does **not**
formalize the paper's
full bidirectional affine-equivalence definition, the rate/minimality and
span arguments that produce a loss basis and Equation (15) from that
definition, an online learner, or a priority claim. In particular, the
repository proves the canonical-normal-form cores of Lemmas 4 and 5 plus the
finite normalized-identity bridges, rather than silently upgrading them to the
paper's full linear-equivalence theorems.

Earlier Blackwell approachability, finite-game, minimax, and norm-conversion
modules remain in the repository as supporting work; they are not part of the
Palomar selection.

## Layout

- `BlackwellIrreducibility.lean` contains the complete proof and the two
  explicit source families.
- `BlackwellChallenge.lean` is the Mathlib-only fifteen-theorem statement surface.
- `BlackwellSolution.lean` supplies checked adapters to the implementation.
- `BlackwellIrreducibilityExamples.lean` exercises both fixed-point families,
  the two generic obstructions, and their concrete no-reduction corollaries.
- `formalization.yaml` records source alignment, scope, and review boundaries.

## Build and verification

The dependency graph is pinned in `lake-manifest.json`.

```bash
lake build
bash scripts/verify-palomar.sh
```

The preparation gate checks the independent Challenge import closure, exact
fifteen-declaration Challenge/Solution surface, implementation-placeholder ban,
source dependency closure, named-theorem axiom allowlist, official renderer
notation audit, metadata alignment, and executable regressions. The pinned
Comparator/NanoDa replay is available through `scripts/verify-comparator.sh`.
macOS requires the explicit `PALOMAR_ALLOW_UNSANDBOXED_LOCAL=1` fallback because
Landrun's kernel sandbox is Linux-only; hosted verification uses real Landrun.

## Attribution

> Christoph Dann, Yishay Mansour, Mehryar Mohri, Jon Schneider, and
> Balasubramanian Sivan. “Rate-Preserving Reductions for Blackwell
> Approachability.” *Proceedings of the Thirty Eighth Conference on Learning
> Theory*, PMLR 291:1380–1414, 2025.

The formalization follows the source constructions and credits them
accordingly. AI assistance was used for proof engineering. The final
definitions, statements, and proofs are checked by Lean.
