# Development notes

## Finite source specialization

The source theorem uses a convex family `U` of bilinear constraints and the
tensor action space `U tensor P`. This project fixes the finite setting in
which `U = Delta_m` is the convex hull of `m` coordinate constraints and
`P = Delta_n`. Its tensor realization is the joint simplex `Delta_(m x n)`.
That representation is exactly the convex hull of rank-one product tables:
coordinate vertices are point-mass outer products, and every joint action is
a finite convex combination of those vertices. It has a canonical action
marginal. The central objective, improperness, and
reduction APIs require `[Nonempty m]` and `[Nonempty n]`. These assumptions
make both simplexes and both online-strategy codomains genuinely inhabited;
an explicit anchor witnesses the same fact for `m`, but the typeclass remains
in the public signature so the scope is visible and uniform.

`Payoff m n d` stores the finite coordinates of the bilinear functions. For a
loss `l`, `reducedLoss` is the vector representation of `M_B l` for

```text
B(x,l) = - sum_(i,j,k) x(i,j) payoff(i,j,k) l(k).
```

`score u w p l` is deliberately defined through the same pairing, so the
central identity is a short, audited additive-bilinearity argument rather
than a fragile expansion of nested finite sums.

## Proof architecture

1. `outer_jointSimplex`, `elementaryTensor_eq_outer_pointMass`, and
   `jointSimplex_eq_finiteTensorCombination` establish the finite tensor-hull
   representation; `marginal_simplex` and `marginal_outer` establish the legal
   action maps `decode` and `lift`.
2. `shift_not_jointSimplex` proves improperness by total mass: an allowed
   joint action and the added rank-one table each have mass one.
3. `pairing_shift_sub_pairing_eq_score` proves the per-round identity.
4. `regretSum_eq_approachSum` lifts it to any finite horizon, and
   `regretLoss_eq_approachLoss` lifts it to the supremum objective.
5. `liftStrategy` and `decodeStrategy` accept a list of prior losses, so both
   translations are causal by their types. The algorithmic theorem combines
   their trajectory equalities with the same loss history.

The public Challenge contains exactly eleven intentional holes: the tensor
representation, action-set lemmas, improperness, one-step and horizon
identities, trajectory equality, and both trajectory- and strategy-level
tightness results. The Solution
contains no proof placeholder. The shape gate also inspects every central
declaration and fails if either nonemptiness assumption is removed.

## Boundary

The coordinate decomposition is specific to this finite simplex model; it is
not an arbitrary tensor-product or convex-set theorem. The development also
does not formalize stochastic
strategies, an algorithmic complexity bound, existence of a maximizing mixed
constraint, or an asymptotic rate infimum. The source paper's broader theorem
is cited as the mathematical origin; this development makes the finite
simplex construction and its exact causal loss identities independently
checkable.
