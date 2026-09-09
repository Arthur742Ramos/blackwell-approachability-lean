import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.Sion
import Mathlib.Tactic

set_option autoImplicit false

/-
# Independent statement surface

The Challenge module intentionally imports only Mathlib. It states the
certificate, its quantitative error-robust extension, and a finite-action
strategic theorem. The strategic theorem constructs a Markov response from a
pointwise Blackwell response condition and quantifies over every opponent
sequence. The proof placeholders are the mechanical comparison targets; the
checked proofs live in BlackwellSolution.lean and the implementation modules.
-/

namespace Blackwell.Palomar

open scoped BigOperators

/-- The real scalar action supplied by the inner-product-space instance.
    Naming it keeps the independent Challenge signature stable under isolated
    pretty-printing. -/
def real_smul {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (r : ℝ) (x : E) : E := r • x

/-- The usual Mathlib convexity predicate for the real scalar action. -/
def real_convex {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (C : Set E) : Prop := Convex ℝ C

structure Mixed (A : Type*) [Fintype A] where
  weight : A → ℝ
  nonneg : ∀ a, 0 ≤ weight a
  sum_weight : ∑ a, weight a = 1

noncomputable def expectedPayoff {A B E : Type*} [Fintype A]
    [AddCommMonoid E] [Module ℝ E]
    (p : Mixed A) (g : A → B → E) (b : B) : E :=
  ∑ a, p.weight a • g a b

/-- A closest point to `y` in a nonempty closed convex target, together with
    the normal-cone inequality for every target point. -/
theorem exists_projection {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] {C : Set E}
    (hne : C.Nonempty) (hclosed : IsClosed C) (hconvex : real_convex C)
    (y : E) :
    ∃ p ∈ C, ‖y - p‖ = Metric.infDist y C ∧
      ∀ z ∈ C, inner ℝ (y - p) (z - p) ≤ 0 := by
  sorry

/-- Sion's minimax theorem turns feasibility against each opponent mixed
    action into one response that works uniformly against the whole opponent
    action set. -/
theorem exists_uniform_response_of_sion
    {E F : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    {X : Set E} {Y : Set F} (f : E → F → ℝ)
    (ne_X : X.Nonempty) (cX : Convex ℝ X) (kX : IsCompact X)
    (hfy : ∀ y ∈ Y, LowerSemicontinuousOn (fun x => f x y) X)
    (hfy' : ∀ y ∈ Y, QuasiconvexOn ℝ X (fun x => f x y))
    [TopologicalSpace F] [AddCommGroup F] [Module ℝ F]
    [IsTopologicalAddGroup F] [ContinuousSMul ℝ F]
    (cY : Convex ℝ Y) (ne_Y : Y.Nonempty) (kY : IsCompact Y)
    (hfx : ∀ x ∈ X, UpperSemicontinuousOn (fun y => f x y) Y)
    (hfx' : ∀ x ∈ X, QuasiconcaveOn ℝ Y (fun y => f x y))
    (hfeasible : ∀ y ∈ Y, ∃ x ∈ X, f x y ≤ 0) :
    ∃ x ∈ X, ∀ y ∈ Y, f x y ≤ 0 := by
  sorry

noncomputable def closestPoint {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] {C : Set E}
    (hne : C.Nonempty) (hclosed : IsClosed C) (hconvex : real_convex C) : E → E :=
  fun y => Classical.choose (exists_projection hne hclosed hconvex y)

noncomputable def adaptiveAverage {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    (stage : ℕ → E → E) : ℕ → E
  | 0 => 0
  | t + 1 => real_smul (((t : ℝ) + 1)⁻¹)
      (real_smul (t : ℝ) (adaptiveAverage stage t) +
        stage t (adaptiveAverage stage t))

/-- A conditional finite-time distance bound from the Blackwell
    supporting-half-space certificate. -/
theorem blackwell_approachability_bound {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {C : Set E} (x avg proj : ℕ → E) (B : ℝ)
    (hproj : ∀ t : ℕ, proj t ∈ C)
    (hmin : ∀ t : ℕ, ∀ z ∈ C,
      ‖avg t - proj t‖ ≤ ‖avg t - z‖)
    (havg : ∀ t : ℕ, real_smul ((t : ℝ) + 1) (avg (t + 1)) =
      real_smul (t : ℝ) (avg t) + x t)
    (hinner : ∀ t : ℕ,
      inner ℝ (avg t - proj t) (x t - proj t) ≤ 0)
    (hbound : ∀ t : ℕ, ‖x t - proj t‖ ≤ B) (hB : 0 ≤ B) :
    ∀ {T : ℕ}, 0 < T →
      Metric.infDist (avg T) C ≤ B / Real.sqrt T := by
  sorry

/-- The certificate with a uniform additive error in the supporting
    half-space inequality. -/
theorem blackwell_approximate_bound {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {C : Set E} (x avg proj : ℕ → E)
    (B epsilon : ℝ) (hproj : ∀ t : ℕ, proj t ∈ C)
    (hmin : ∀ t : ℕ, ∀ z ∈ C,
      ‖avg t - proj t‖ ≤ ‖avg t - z‖)
    (havg : ∀ t : ℕ, real_smul ((t : ℝ) + 1) (avg (t + 1)) =
      real_smul (t : ℝ) (avg t) + x t)
    (hinner : ∀ t : ℕ,
      inner ℝ (avg t - proj t) (x t - proj t) ≤ epsilon)
    (hbound : ∀ t : ℕ, ‖x t - proj t‖ ≤ B)
    (hepsilon : 0 ≤ epsilon) :
    ∀ {T : ℕ}, 0 < T →
      Metric.infDist (avg T) C ≤ Real.sqrt (B ^ 2 / T + epsilon) := by
  sorry

noncomputable def gameAverage {A B E : Type*} [Fintype A]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (g : A → B → E) (strategy : E → A) (opponent : ℕ → B) : ℕ → E :=
  adaptiveAverage (fun t y => g (strategy y) (opponent t))

noncomputable def mixedGameAverage {A B E : Type*} [Fintype A]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (g : A → B → E) (strategy : E → Mixed A) (opponent : ℕ → B) : ℕ → E :=
  adaptiveAverage
    (fun t y => expectedPayoff (strategy y) g (opponent t))

/-- Pointwise choice turns the game-level Blackwell response condition into
    an actual strategy function. -/
theorem exists_pure_pointwise_strategy
    {A B E : Type*} [Fintype A] [Fintype B]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (g : A → B → E) {C : Set E}
    (hne : C.Nonempty) (hclosed : IsClosed C) (hconvex : real_convex C)
    (Bnd epsilon : ℝ)
    (hresponse : ∀ y : E, ∃ a : A, ∀ b : B,
      inner ℝ (y - closestPoint hne hclosed hconvex y)
          (g a b - closestPoint hne hclosed hconvex y) ≤ epsilon ∧
      ‖g a b - closestPoint hne hclosed hconvex y‖ ≤ Bnd) :
    ∃ strategy : E → A, ∀ y : E, ∀ b : B,
      inner ℝ (y - closestPoint hne hclosed hconvex y)
          (g (strategy y) b - closestPoint hne hclosed hconvex y) ≤ epsilon ∧
      ‖g (strategy y) b - closestPoint hne hclosed hconvex y‖ ≤ Bnd := by
  sorry

/-- Finite-action Blackwell approachability with explicit strategy existence.
    The conclusion holds against every opponent action sequence. -/
theorem pure_game_approachability_of_response
    {A B E : Type*} [Fintype A] [Fintype B]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (g : A → B → E) {C : Set E}
    (hne : C.Nonempty) (hclosed : IsClosed C) (hconvex : real_convex C)
    (Bnd epsilon : ℝ)
    (hresponse : ∀ y : E, ∃ a : A, ∀ b : B,
      inner ℝ (y - closestPoint hne hclosed hconvex y)
          (g a b - closestPoint hne hclosed hconvex y) ≤ epsilon ∧
      ‖g a b - closestPoint hne hclosed hconvex y‖ ≤ Bnd)
    (hepsilon : 0 ≤ epsilon) :
    ∃ strategy : E → A, ∀ opponent : ℕ → B, ∀ {T : ℕ}, 0 < T →
      Metric.infDist (gameAverage g strategy opponent T) C ≤
        Real.sqrt (Bnd ^ 2 / T + epsilon) := by
  sorry

/-- The finite-game statement with mixed actions, matching the usual
    vector-payoff formulation of Blackwell approachability. -/
theorem mixed_game_approachability_of_response
    {A B E : Type*} [Fintype A] [Fintype B]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (g : A → B → E) {C : Set E}
    (hne : C.Nonempty) (hclosed : IsClosed C) (hconvex : real_convex C)
    (Bnd epsilon : ℝ)
    (hresponse : ∀ y : E, ∃ p : Mixed A, ∀ b : B,
      inner ℝ (y - closestPoint hne hclosed hconvex y)
          (expectedPayoff p g b - closestPoint hne hclosed hconvex y) ≤ epsilon ∧
      ‖expectedPayoff p g b - closestPoint hne hclosed hconvex y‖ ≤ Bnd)
    (hepsilon : 0 ≤ epsilon) :
    ∃ strategy : E → Mixed A, ∀ opponent : ℕ → B, ∀ {T : ℕ}, 0 < T →
      Metric.infDist (mixedGameAverage g strategy opponent T) C ≤
        Real.sqrt (Bnd ^ 2 / T + epsilon) := by
  sorry

/-- The pointwise mixed response hypothesis has an explicit strategy
    realization by classical choice. -/
theorem exists_mixed_pointwise_strategy
    {A B E : Type*} [Fintype A] [Fintype B]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (g : A → B → E) {C : Set E}
    (hne : C.Nonempty) (hclosed : IsClosed C) (hconvex : real_convex C)
    (Bnd epsilon : ℝ)
    (hresponse : ∀ y : E, ∃ p : Mixed A, ∀ b : B,
      inner ℝ (y - closestPoint hne hclosed hconvex y)
          (expectedPayoff p g b - closestPoint hne hclosed hconvex y) ≤ epsilon ∧
      ‖expectedPayoff p g b - closestPoint hne hclosed hconvex y‖ ≤ Bnd) :
    ∃ strategy : E → Mixed A, ∀ y : E, ∀ b : B,
      inner ℝ (y - closestPoint hne hclosed hconvex y)
          (expectedPayoff (strategy y) g b - closestPoint hne hclosed hconvex y) ≤ epsilon ∧
      ‖expectedPayoff (strategy y) g b - closestPoint hne hclosed hconvex y‖ ≤ Bnd := by
  sorry

noncomputable def l2Norm {A : Type*} [Fintype A] (v : A → ℝ) : ℝ :=
  Real.sqrt (∑ a, v a ^ 2)

noncomputable def averageRegret {A : Type*} [Fintype A]
    (loss : ℕ → A → ℝ) (actions : ℕ → A) (T : ℕ) : A → ℝ :=
  fun a => (T : ℝ)⁻¹ *
    ∑ t ∈ Finset.range T, (loss t (actions t) - loss t a)

/-- A Euclidean approachability certificate for the regret vector implies a
    coordinatewise no-regret bound. -/
theorem regret_coordinate_of_l2_bound {A : Type*} [Fintype A]
    (loss : ℕ → A → ℝ) (actions : ℕ → A) (T : ℕ) (delta : ℝ)
    (hdelta : l2Norm (averageRegret loss actions T) ≤ delta) :
    ∀ a : A, averageRegret loss actions T a ≤ delta := by
  sorry

theorem l2_bound_of_coordinate_bound {A : Type*} [Fintype A]
    (v : A → ℝ) (rho : ℝ) (hrho : 0 ≤ rho)
    (hcoord : ∀ a : A, |v a| ≤ rho) :
    l2Norm v ≤ Real.sqrt (Fintype.card A) * rho := by
  sorry

/-- The reverse ℓ2-to-coordinate conversion necessarily carries a finite
    action-set factor; the factor is attained by a constant regret vector. -/
theorem dimension_factor_is_attained {A : Type*} [Fintype A] (rho : ℝ)
    (hrho : 0 ≤ rho) :
    l2Norm (fun _ : A => rho) = Real.sqrt (Fintype.card A) * rho := by
  sorry

end Blackwell.Palomar
