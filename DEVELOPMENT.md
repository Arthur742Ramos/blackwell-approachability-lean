# Development notes

`BlackwellChallenge.lean` is intentionally independent from the implementation:
it imports only Mathlib and carries exactly eleven proof placeholders, one for
each selected declaration. `BlackwellSolution.lean` imports the checked
implementation and contains no placeholders. The Challenge names
`real_smul`, `real_convex`, the finite `Mixed` type, and the average/regret
surfaces explicitly so its signatures remain stable under isolated theorem
printing.

The core certificate is organized around

```text
(t + 1)^2 e_(t+1)^2 <= t^2 e_t^2 + B^2,
```

where `e_t` is the distance from the running average to its closest target
point. Induction gives `t^2 e_t^2 <= t B^2`; the nonnegative square-root
comparison gives the `B / sqrt T` rate. The approximate theorem tracks the
additional `2 * t * epsilon` cross term and records the non-vanishing error
floor.

`BlackwellGame.lean` makes the sequential structure explicit. A finite mixed
action is a nonnegative probability vector, the opponent supplies a pure
action at each round, and the player's strategy is a function of the current
average. Pointwise choice turns a response relation into a strategy, after
which the geometric certificate is applied to every opponent sequence. Both
pure and mixed response versions are included.

`BlackwellMinimax.lean` isolates the compact-convex Sion argument. It is
deliberately stated with its continuity, quasiconvexity, compactness, and
feasibility hypotheses visible; it is not presented as an automatic proof of a
particular game's response condition.

`BlackwellReduction.lean` isolates the finite-dimensional part of the
approachability/no-regret connection. Coordinate control follows directly
from `l2` control, while coordinatewise control implies an `l2` bound with a
`sqrt (card A)` factor. The constant-vector theorem records sharpness rather
than hiding this dimension dependence.

The projection theorem reuses Mathlib's Hilbert projection result and its
inner-product characterization of minimizers. The examples include a nonzero
sequence that starts outside a singleton target and then cancels back to it,
a mixed finite game, a pure finite game, and regret-coordinate conversion. No
custom axiom, unsafe declaration, or non-Mathlib dependency is used.

The Palomar-facing scalar and convexity wrappers are definitionally ordinary
Mathlib operations. They exist to keep the independent surface robust when a
trusted notation audit prints declarations in isolation.
