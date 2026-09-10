# Development notes

## Finite source specialization

The source theorem uses a convex family `U` of bilinear constraints and the
tensor action space `U tensor P`. This project fixes the finite setting in
which `U = Delta_m` is the convex hull of `m` coordinate constraints and
`P = Delta_n`. Its tensor realization is the joint simplex `Delta_(m x n)`.
That representation is exactly the convex hull of rank-one product tables and
has a canonical action marginal.

`Payoff m n d` stores the finite coordinates of the bilinear functions. For a
loss `l`, `reducedLoss` is the vector representation of `M_B l` for

```text
B(x,l) = - sum_(i,j,k) x(i,j) payoff(i,j,k) l(k).
```

`score u w p l` is deliberately defined through the same pairing, so the
central identity is a short, audited additive-bilinearity argument rather
than a fragile expansion of nested finite sums.

## Proof architecture

1. `marginal_simplex`, `outer_jointSimplex`, and `marginal_outer` establish
   the legal action maps `decode` and `lift`.
2. `shift_not_jointSimplex` proves improperness by total mass: an allowed
   joint action and the added rank-one table each have mass one.
3. `pairing_shift_sub_pairing_eq_score` proves the per-round identity.
4. `regretSum_eq_approachSum` lifts it to any finite horizon, and
   `regretLoss_eq_approachLoss` lifts it to the supremum objective.
5. `liftStrategy` and `decodeStrategy` accept a list of prior losses, so both
   translations are causal by their types. The algorithmic theorem combines
   their trajectory equalities with the same loss history.

The public Challenge contains exactly nine intentional holes: the action-set
lemmas, improperness, one-step and horizon identities, trajectory equality,
and both trajectory- and strategy-level tightness results. The Solution
contains no proof placeholder.

## Boundary

The concrete finite model avoids asserting an arbitrary tensor decomposition
or arbitrary convex-set theorem. It also does not formalize stochastic
strategies, an algorithmic complexity bound, existence of a maximizing mixed
constraint, or an asymptotic rate infimum. The source paper's broader theorem
is cited as the mathematical origin; this development makes the finite
simplex construction and its exact causal loss identities independently
checkable.
