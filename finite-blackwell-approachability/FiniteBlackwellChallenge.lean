import Mathlib

set_option autoImplicit false

namespace Blackwell.FiniteApproachability.Palomar

open Set
open scoped BigOperators

universe u

abbrev FiniteEuclideanSpace (I : Type u) : Type u := I → ℝ

noncomputable section

/-- The standard coordinate dot product on a finite real Euclidean space. -/
def coordinateInner {I : Type*} [Fintype I]
    (x y : (I → ℝ)) : ℝ :=
  ∑ i, x i * y i

/-- The Euclidean norm written directly in finite coordinates. -/
def coordinateNorm {I : Type*} [Fintype I]
    (x : (I → ℝ)) : ℝ :=
  Real.sqrt (∑ i, x i ^ 2)

/-- The Euclidean distance written directly in finite coordinates. -/
def coordinateDistance {I : Type*} [Fintype I]
    (x y : (I → ℝ)) : ℝ :=
  coordinateNorm (x - y)

/-- Distance to a set, as the infimum of the finite-coordinate distances. -/
noncomputable def coordinateInfDist {I : Type*} [Fintype I]
    (x : (I → ℝ)) (C : Set (I → ℝ)) : ℝ :=
  ⨅ z : C, coordinateDistance x z.1

/-- Probability vectors on a finite action type. -/
def simplex {α : Type*} [Fintype α] (p : α → ℝ) : Prop :=
  (∀ a, 0 ≤ p a) ∧ (∑ a, p a) = 1

/-- The finite mixed-action simplex as a subset of its coordinate space. -/
def simplexSet (α : Type*) [Fintype α] : Set (α → ℝ) :=
  {p | simplex p}

/-- A bundled finite mixed action. -/
abbrev Mixed (α : Type*) [Fintype α] := {p : α → ℝ // simplex p}

/-- A closest-point witness and its normal-cone inequality. -/
theorem exists_projection {I : Type*} [Fintype I]
    {C : Set (I → ℝ)}
    (hne : C.Nonempty) (hclosed : IsClosed C) (hconvex : Convex ℝ C)
    (y : (I → ℝ)) :
    ∃ p ∈ C, coordinateDistance y p = coordinateInfDist y C ∧
      ∀ z ∈ C, coordinateInner (y - p) (z - p) ≤ 0 := by
  sorry

/-- A chosen nearest point in a nonempty closed convex target. -/
noncomputable def closestPoint {I : Type*} [Fintype I]
    {C : Set (I → ℝ)}
    (hne : C.Nonempty) (hclosed : IsClosed C) (hconvex : Convex ℝ C) :
    (I → ℝ) → (I → ℝ) :=
  fun y => Classical.choose (exists_projection hne hclosed hconvex y)

/-- The chosen nearest point lies in the target. -/
lemma closestPoint_mem {I : Type*} [Fintype I]
    {C : Set (I → ℝ)}
    (hne : C.Nonempty) (hclosed : IsClosed C) (hconvex : Convex ℝ C)
    (y : (I → ℝ)) : closestPoint hne hclosed hconvex y ∈ C :=
  (Classical.choose_spec (exists_projection hne hclosed hconvex y)).1

/-- Expected payoff against one pure opponent action. -/
def expectedPayoff {A B I : Type*} [Fintype A] [Fintype I]
    (p : A → ℝ) (g : A → B → (I → ℝ)) (b : B) :
    (I → ℝ) :=
  ∑ a, p a • g a b

/-- Expected payoff when both players use mixed actions. -/
def mixedExpectedPayoff {A B I : Type*} [Fintype A] [Fintype B] [Fintype I]
    (p : A → ℝ) (q : B → ℝ) (g : A → B → (I → ℝ)) :
    (I → ℝ) :=
  ∑ b, q b • expectedPayoff p g b

/-- Scalar supporting-half-space score computed in finite coordinates. -/
def normalScore {A B I : Type*} [Fintype A] [Fintype B] [Fintype I]
    (g : A → B → (I → ℝ)) (y z : (I → ℝ))
    (p : A → ℝ) (q : B → ℝ) : ℝ :=
  coordinateInner (y - z) (mixedExpectedPayoff p q g)

/-- Every mixed opponent action admits a feasible mixed response. -/
abbrev mixedBlackwellCondition {A B I : Type*} [Fintype A] [Fintype B]
    [Fintype I] [Nonempty A] [Nonempty B] [Nonempty I]
    (g : A → B → (I → ℝ)) {C : Set (I → ℝ)}
    (hne : C.Nonempty) (hclosed : IsClosed C) (hconvex : Convex ℝ C) : Prop :=
  ∀ y : (I → ℝ), ∀ q : B → ℝ, q ∈ simplexSet B →
    ∃ p : A → ℝ, p ∈ simplexSet A ∧
      normalScore g y (closestPoint hne hclosed hconvex y) p q ≤
        coordinateInner (y - closestPoint hne hclosed hconvex y)
          (closestPoint hne hclosed hconvex y)

/--
Sion minimax turns pointwise feasibility against each opponent mixture into
one player mixture that works uniformly against every opponent mixture.
-/
theorem exists_uniform_mixed_response {A B I : Type*}
    [Fintype A] [Fintype B] [Fintype I]
    [Nonempty A] [Nonempty B] [Nonempty I]
    (g : A → B → (I → ℝ))
    (y z : (I → ℝ))
    (hfeasible : ∀ q : B → ℝ, q ∈ simplexSet B →
      ∃ p : A → ℝ, p ∈ simplexSet A ∧
        normalScore g y z p q ≤ coordinateInner (y - z) z) :
    ∃ p : A → ℝ, p ∈ simplexSet A ∧
      ∀ q : B → ℝ, q ∈ simplexSet B →
        normalScore g y z p q ≤ coordinateInner (y - z) z := by
  sorry

/-- Expected running payoff against a pure opponent-action sequence. -/
def adaptiveAverage {I : Type*} [Fintype I]
    (stage : ℕ → (I → ℝ) → (I → ℝ)) :
    ℕ → (I → ℝ)
  | 0 => 0
  | t + 1 => ((t : ℝ) + 1)⁻¹ •
      ((t : ℝ) • adaptiveAverage stage t + stage t (adaptiveAverage stage t))

/-- Average expected payoff against an arbitrary pure opponent sequence. -/
def gameAverage {A B I : Type*} [Fintype A] [Fintype I]
    (g : A → B → (I → ℝ))
    (strategy : (I → ℝ) → {p : A → ℝ // simplex p})
    (opponent : ℕ → B) : ℕ → (I → ℝ) :=
  adaptiveAverage (fun t y =>
    expectedPayoff (strategy y).1 g (opponent t))

/--
A forcing response with bounded displacement gives the finite-time
Euclidean approachability rate.
-/
theorem finite_game_approachability_bound
    {A B I : Type*} [Fintype A] [Fintype B] [Fintype I]
    [Nonempty A] [Nonempty B] [Nonempty I]
    (g : A → B → (I → ℝ))
    (strategy : (I → ℝ) → {p : A → ℝ // simplex p})
    {C : Set (I → ℝ)}
    (hne : C.Nonempty) (hclosed : IsClosed C) (hconvex : Convex ℝ C)
    (Bnd : ℝ)
    (hforce : ∀ y : (I → ℝ), ∀ b : B,
      coordinateInner (y - closestPoint hne hclosed hconvex y)
        (expectedPayoff (strategy y).1 g b - closestPoint hne hclosed hconvex y) ≤ 0)
    (hbound : ∀ y : (I → ℝ), ∀ b : B,
      coordinateNorm (expectedPayoff (strategy y).1 g b -
        closestPoint hne hclosed hconvex y) ≤ Bnd)
    (hBnd : 0 ≤ Bnd) (opponent : ℕ → B) :
    ∀ {T : ℕ}, 0 < T →
      coordinateInfDist (gameAverage g strategy opponent T) C ≤ Bnd / Real.sqrt T := by
  sorry

/--
From mixed Blackwell feasibility, bounded payoffs, and a bounded nonempty
closed convex target, a causal mixed strategy achieves the explicit
(G + R) / sqrt(T) expected-average approachability rate.
-/
theorem finite_game_approachability_of_mixedBlackwell
    {A B I : Type*} [Fintype A] [Fintype B] [Fintype I]
    [Nonempty A] [Nonempty B] [Nonempty I]
    (g : A → B → (I → ℝ))
    {C : Set (I → ℝ)}
    (hne : C.Nonempty) (hclosed : IsClosed C) (hconvex : Convex ℝ C)
    (G R : ℝ) (hG : 0 ≤ G) (hR : 0 ≤ R)
    (hpay : ∀ a b, coordinateNorm (g a b) ≤ G)
    (hradius : ∀ z ∈ C, coordinateNorm z ≤ R)
    (hblackwell : mixedBlackwellCondition g hne hclosed hconvex) :
    ∃ strategy : (I → ℝ) → {p : A → ℝ // simplex p},
      ∀ opponent : ℕ → B, ∀ {T : ℕ}, 0 < T →
      coordinateInfDist (gameAverage g strategy opponent T) C ≤
        (G + R) / Real.sqrt T := by
  sorry

end

end Blackwell.FiniteApproachability.Palomar
