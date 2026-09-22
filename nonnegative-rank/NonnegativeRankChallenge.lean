import Mathlib.Data.Real.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Ring.Finset

set_option autoImplicit false

open scoped BigOperators

namespace Blackwell.NonnegativeRank.Palomar

universe u v

/-- A finite probability table: nonnegative entries with total mass one. -/
def IsProbabilityMatrix {m : Type u} {n : Type v}
    [Fintype m] [Fintype n] (P : m → n → ℝ) : Prop :=
  (∀ i j, 0 ≤ P i j) ∧ (∑ i, ∑ j, P i j) = 1

/-- An exact nonnegative factorization with `k` latent components. -/
def HasNonnegativeFactorization {m : Type u} {n : Type v}
    [Fintype m] [Fintype n] (P : m → n → ℝ) (k : ℕ) : Prop :=
  ∃ U : m → Fin k → ℝ, ∃ V : Fin k → n → ℝ,
    (∀ i r, 0 ≤ U i r) ∧
    (∀ r j, 0 ≤ V r j) ∧
    (∀ i j, P i j = ∑ r, U i r * V r j)

/-- A mixture of `k` independent product distributions on the two coordinates. -/
def HasProductMixture {m : Type u} {n : Type v}
    [Fintype m] [Fintype n] (P : m → n → ℝ) (k : ℕ) : Prop :=
  ∃ w : Fin k → ℝ, ∃ p : Fin k → m → ℝ, ∃ q : Fin k → n → ℝ,
    (∀ r, 0 ≤ w r) ∧
    (∑ r, w r) = 1 ∧
    (∀ r i, 0 ≤ p r i) ∧
    (∀ r, ∑ i, p r i = 1) ∧
    (∀ r j, 0 ≤ q r j) ∧
    (∀ r, ∑ j, q r j = 1) ∧
    (∀ i j, P i j = ∑ r, w r * p r i * q r j)

/-- `k` is the least component count among exact nonnegative factorizations of `P`. -/
def IsLeastNonnegativeFactorizationCount {m : Type u} {n : Type v}
    [Fintype m] [Fintype n] (P : m → n → ℝ) (k : ℕ) : Prop :=
  HasNonnegativeFactorization P k ∧
    ∀ ℓ, HasNonnegativeFactorization P ℓ → k ≤ ℓ

/-- `k` is the least number of independent product distributions mixing to `P`. -/
def IsLeastProductMixtureCount {m : Type u} {n : Type v}
    [Fintype m] [Fintype n] (P : m → n → ℝ) (k : ℕ) : Prop :=
  HasProductMixture P k ∧ ∀ ℓ, HasProductMixture P ℓ → k ≤ ℓ

/-- A set of positive cells whose pairs cannot be covered by one positive rank-one term. -/
def IsFoolingSet {m : Type u} {n : Type v}
    [Fintype m] [Fintype n] (P : m → n → ℝ) (ℓ : ℕ)
    (f : Fin ℓ → m × n) : Prop :=
  Function.Injective f ∧
    (∀ s, 0 < P (f s).1 (f s).2) ∧
    (∀ s t, s ≠ t →
      P (f s).1 (f t).2 = 0 ∨ P (f t).1 (f s).2 = 0)

/-- The uniform probability distribution supported on the diagonal of `Fin N × Fin N`. -/
noncomputable def uniformDiagonal (N : ℕ) (i j : Fin N) : ℝ :=
  if i = j then (N : ℝ)⁻¹ else 0

/-- Product-mixture size is exactly nonnegative-factorization size at every fixed component count.

The probability normalization is essential: it lets each nonzero factor be normalized into two
probability vectors, while zero factors are replaced by point masses and assigned weight zero.
-/
theorem productMixture_iff_nonnegativeFactorization
    {m : Type u} {n : Type v} [Fintype m] [Fintype n]
    [Nonempty m] [Nonempty n] (P : m → n → ℝ)
    (hP : IsProbabilityMatrix P) (k : ℕ) :
    HasProductMixture P k ↔ HasNonnegativeFactorization P k := by
  sorry

/-- The least feasible component counts agree for product mixtures and nonnegative factorizations.
-/
theorem leastProductMixtureCount_iff_leastNonnegativeFactorizationCount
    {m : Type u} {n : Type v} [Fintype m] [Fintype n]
    [Nonempty m] [Nonempty n] (P : m → n → ℝ)
    (hP : IsProbabilityMatrix P) (k : ℕ) :
    IsLeastProductMixtureCount P k ↔ IsLeastNonnegativeFactorizationCount P k := by
  sorry

/-- Every fooling set of positive cells needs a distinct component in any nonnegative factorization.
-/
theorem foolingSet_card_le_factorCount
    {m : Type u} {n : Type v} [Fintype m] [Fintype n]
    {P : m → n → ℝ} {ℓ k : ℕ} {f : Fin ℓ → m × n}
    (hF : IsFoolingSet P ℓ f)
    (hfactor : HasNonnegativeFactorization P k) : ℓ ≤ k := by
  sorry

/-- The uniform diagonal table has a product-mixture representation with `N` components. -/
theorem uniformDiagonal_has_productMixture
    {N : ℕ} (hN : 0 < N) :
    HasProductMixture (uniformDiagonal N) N := by
  sorry

/-- No mixture with fewer than `N` product components represents the uniform diagonal table. -/
theorem uniformDiagonal_mixture_minimal
    {N k : ℕ} (hN : 0 < N)
    (hmixture : HasProductMixture (uniformDiagonal N) k) : N ≤ k := by
  sorry

end Blackwell.NonnegativeRank.Palomar
