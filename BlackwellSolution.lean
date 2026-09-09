import BlackwellApproachability
import BlackwellGame
import BlackwellReduction
import BlackwellMinimax

set_option autoImplicit false

/-
# Proof surface

The selected declarations mirror BlackwellChallenge.lean exactly. Their
proofs are short adapters to the independently named implementation facts.
-/

namespace Blackwell.Palomar

open scoped BigOperators

/-- The real scalar action supplied by the inner-product-space instance.
    Naming it keeps the proof surface definitionally aligned with the
    independent Challenge signature. -/
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
  exact Blackwell.Approachability.exists_projection hne hclosed
    (by simpa [real_convex] using hconvex) y

noncomputable def closestPoint {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] {C : Set E}
    (hne : C.Nonempty) (hclosed : IsClosed C) (hconvex : real_convex C) : E → E :=
  fun y => Classical.choose (exists_projection hne hclosed hconvex y)

lemma closestPoint_spec {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] {C : Set E}
    (hne : C.Nonempty) (hclosed : IsClosed C) (hconvex : real_convex C) (y : E) :
    closestPoint hne hclosed hconvex y ∈ C ∧
      ‖y - closestPoint hne hclosed hconvex y‖ = Metric.infDist y C ∧
      ∀ z ∈ C, inner ℝ (y - closestPoint hne hclosed hconvex y)
        (z - closestPoint hne hclosed hconvex y) ≤ 0 := by
  simpa [closestPoint, real_convex] using
    Classical.choose_spec (Blackwell.Approachability.exists_projection hne hclosed
      (by simpa [real_convex] using hconvex) y)

noncomputable def adaptiveAverage {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    (stage : ℕ → E → E) : ℕ → E
  | 0 => 0
  | t + 1 => real_smul (((t : ℝ) + 1)⁻¹)
      (real_smul (t : ℝ) (adaptiveAverage stage t) +
        stage t (adaptiveAverage stage t))

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
  intro T hT
  apply Blackwell.Approachability.blackwell_approachability_bound
    x avg proj B hproj hmin ?_ hinner hbound hB (T := T) hT
  intro t
  simpa [real_smul] using havg t

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
    (hB : 0 ≤ B) (hepsilon : 0 ≤ epsilon) :
    ∀ {T : ℕ}, 0 < T →
      Metric.infDist (avg T) C ≤ Real.sqrt (B ^ 2 / T + epsilon) := by
  intro T hT
  apply Blackwell.Approachability.blackwell_approximate_bound
    x avg proj B epsilon hproj hmin ?_ hinner hbound hB hepsilon
    (T := T) hT
  intro t
  simpa [real_smul] using havg t

noncomputable def gameAverage {A B E : Type*} [Fintype A]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (g : A → B → E) (strategy : E → A) (opponent : ℕ → B) : ℕ → E :=
  adaptiveAverage (fun t y => g (strategy y) (opponent t))

noncomputable def mixedGameAverage {A B E : Type*} [Fintype A]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (g : A → B → E) (strategy : E → Mixed A) (opponent : ℕ → B) : ℕ → E :=
  adaptiveAverage (fun t y => expectedPayoff (strategy y) g (opponent t))

def toGameMixed {A : Type*} [Fintype A] (p : Mixed A) : Blackwell.Game.Mixed A :=
  { weight := p.weight
    nonneg := p.nonneg
    sum_weight := p.sum_weight }

def fromGameMixed {A : Type*} [Fintype A]
    (p : Blackwell.Game.Mixed A) : Mixed A :=
  { weight := p.weight
    nonneg := p.nonneg
    sum_weight := p.sum_weight }

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
  let strategy : E → A := fun y => Classical.choose (hresponse y)
  refine ⟨strategy, ?_⟩
  intro y b
  exact Classical.choose_spec (hresponse y) b

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
    (hB : 0 ≤ Bnd) (hepsilon : 0 ≤ epsilon) :
    ∃ strategy : E → A, ∀ opponent : ℕ → B, ∀ {T : ℕ}, 0 < T →
      Metric.infDist (gameAverage g strategy opponent T) C ≤
        Real.sqrt (Bnd ^ 2 / T + epsilon) := by
  let hconvex' : Convex ℝ C := by simpa [real_convex] using hconvex
  have hresponse' : ∀ y : E, ∃ a : A, ∀ b : B,
      inner ℝ (y - Blackwell.Game.closestPoint hne hclosed hconvex' y)
          (g a b - Blackwell.Game.closestPoint hne hclosed hconvex' y) ≤ epsilon ∧
      ‖g a b - Blackwell.Game.closestPoint hne hclosed hconvex' y‖ ≤ Bnd := by
    intro y
    obtain ⟨a, ha⟩ := hresponse y
    refine ⟨a, ?_⟩
    simpa [closestPoint, Blackwell.Game.closestPoint, hconvex, hconvex'] using ha
  obtain ⟨strategy, hstrategy⟩ :=
    Blackwell.Game.pure_game_approachability_of_response g hne hclosed hconvex'
      Bnd epsilon hresponse' hB hepsilon
  refine ⟨strategy, ?_⟩
  intro opponent T hT
  have haverage : ∀ n : ℕ,
      adaptiveAverage (fun t y => g (strategy y) (opponent t)) n =
        Blackwell.Approachability.adaptiveAverage
          (fun t y => g (strategy y) (opponent t)) n := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
        simp [adaptiveAverage, Blackwell.Approachability.adaptiveAverage,
          real_smul, ih]
  have hgame : gameAverage g strategy opponent T =
      Blackwell.Game.pureGameAverage g strategy opponent T := by
    simpa [gameAverage, Blackwell.Game.pureGameAverage] using haverage T
  rw [hgame]
  exact hstrategy opponent (T := T) hT

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
    (hB : 0 ≤ Bnd) (hepsilon : 0 ≤ epsilon) :
    ∃ strategy : E → Mixed A, ∀ opponent : ℕ → B, ∀ {T : ℕ}, 0 < T →
      Metric.infDist (mixedGameAverage g strategy opponent T) C ≤
        Real.sqrt (Bnd ^ 2 / T + epsilon) := by
  let hconvex' : Convex ℝ C := by simpa [real_convex] using hconvex
  have hresponse' : ∀ y : E, ∃ p : Blackwell.Game.Mixed A, ∀ b : B,
      inner ℝ (y - Blackwell.Game.closestPoint hne hclosed hconvex' y)
          (Blackwell.Game.expectedPayoff p g b -
            Blackwell.Game.closestPoint hne hclosed hconvex' y) ≤ epsilon ∧
      ‖Blackwell.Game.expectedPayoff p g b -
        Blackwell.Game.closestPoint hne hclosed hconvex' y‖ ≤ Bnd := by
    intro y
    obtain ⟨p, hp⟩ := hresponse y
    refine ⟨toGameMixed p, ?_⟩
    intro b
    simpa [toGameMixed, expectedPayoff, Blackwell.Game.expectedPayoff,
      closestPoint, Blackwell.Game.closestPoint, hconvex, hconvex'] using hp b
  obtain ⟨gameStrategy, hstrategy⟩ :=
    Blackwell.Game.finite_game_approachability_of_response g hne hclosed hconvex'
      Bnd epsilon hresponse' hB hepsilon
  let strategy : E → Mixed A := fun y => fromGameMixed (gameStrategy y)
  refine ⟨strategy, ?_⟩
  intro opponent T hT
  have haverage : ∀ n : ℕ,
      adaptiveAverage
          (fun t y => expectedPayoff (strategy y) g (opponent t)) n =
        Blackwell.Approachability.adaptiveAverage
          (fun t y => Blackwell.Game.expectedPayoff (gameStrategy y) g
            (opponent t)) n := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
        rw [adaptiveAverage, Blackwell.Approachability.adaptiveAverage]
        rw [ih]
        simp [strategy, fromGameMixed, expectedPayoff,
          Blackwell.Game.expectedPayoff, real_smul]
  have hgame : mixedGameAverage g strategy opponent T =
      Blackwell.Game.gameAverage g gameStrategy opponent T := by
    simpa [mixedGameAverage, Blackwell.Game.gameAverage] using haverage T
  rw [hgame]
  exact hstrategy opponent (T := T) hT

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
  let strategy : E → Mixed A := fun y => Classical.choose (hresponse y)
  refine ⟨strategy, ?_⟩
  intro y b
  exact Classical.choose_spec (hresponse y) b

noncomputable def l2Norm {A : Type*} [Fintype A] (v : A → ℝ) : ℝ :=
  Real.sqrt (∑ a, v a ^ 2)

noncomputable def averageRegret {A : Type*} [Fintype A]
    (loss : ℕ → A → ℝ) (actions : ℕ → A) (T : ℕ) : A → ℝ :=
  fun a => (T : ℝ)⁻¹ *
    ∑ t ∈ Finset.range T, (loss t (actions t) - loss t a)

theorem regret_coordinate_of_l2_bound {A : Type*} [Fintype A]
    (loss : ℕ → A → ℝ) (actions : ℕ → A) (T : ℕ) (delta : ℝ)
    (hdelta : l2Norm (averageRegret loss actions T) ≤ delta) :
    ∀ a : A, averageRegret loss actions T a ≤ delta := by
  intro a
  apply Blackwell.Reduction.regret_coordinate_of_l2_bound
    loss actions T delta
  simpa [l2Norm, averageRegret, Blackwell.Reduction.l2Norm,
    Blackwell.Reduction.averageRegret] using hdelta

theorem l2_bound_of_coordinate_bound {A : Type*} [Fintype A]
    (v : A → ℝ) (rho : ℝ) (hrho : 0 ≤ rho)
    (hcoord : ∀ a : A, |v a| ≤ rho) :
    l2Norm v ≤ Real.sqrt (Fintype.card A) * rho := by
  apply Blackwell.Reduction.l2Norm_le_sqrt_card_mul v rho hrho
  simpa [l2Norm, Blackwell.Reduction.l2Norm] using hcoord

theorem dimension_factor_is_attained {A : Type*} [Fintype A] (rho : ℝ)
    (hrho : 0 ≤ rho) :
    l2Norm (fun _ : A => rho) = Real.sqrt (Fintype.card A) * rho := by
  simpa [l2Norm, Blackwell.Reduction.l2Norm] using
    (Blackwell.Reduction.dimension_factor_is_attained (A := A) rho hrho)

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
  exact Blackwell.Minimax.exists_uniform_response_of_sion f ne_X cX kX
    hfy hfy' cY ne_Y kY hfx hfx' hfeasible

end Blackwell.Palomar
