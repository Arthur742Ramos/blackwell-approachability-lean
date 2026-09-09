# Development notes

BlackwellChallenge.lean is intentionally independent from the implementation:
it imports only Mathlib and carries exactly three proof placeholders, one for
each selected theorem. BlackwellSolution.lean imports the checked
implementation and contains no placeholders.

The core certificate is organized around the recurrence

  (t + 1)^2 e_(t+1)^2 <= t^2 e_t^2 + B^2,

where e_t is the distance from the running average to its closest target point.
Induction gives t^2 e_t^2 <= t B^2, and nonnegativity plus the square-root
identity gives the stated rate.

The `responseAverage` and `blackwell_response_bound` definitions package the
same recurrence for an online response oracle: the next payoff is computed
from the current average. This makes the sequential use of the certificate
explicit while retaining the response condition as a hypothesis.

The target projection theorem is derived from Mathlib's Hilbert projection
theorem and its inner-product characterization of minimizers. It supplies the
geometric normal-cone inequality; it does not supply a game strategy or a
payoff sequence satisfying the Blackwell response condition. The examples
include a nonzero sequence that starts outside the singleton target and then
cancels back to it. No custom axiom, unsafe declaration, or non-Mathlib
dependency is used.
