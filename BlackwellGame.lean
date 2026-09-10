import BlackwellApproachability

set_option autoImplicit false

/-
# A finite-action strategic layer

The geometric certificate is now connected to an actual repeated game.  A
mixed action is a finite probability vector, the opponent supplies one pure
action at each round, and the player's response depends only on the current
running average.  The pointwise Blackwell condition is a premise of the game
theorem; the theorem itself constructs the response strategy and quantifies
over every opponent sequence for a nonempty opponent action type.
-/

namespace Blackwell
namespace Game

open scoped BigOperators RealInnerProductSpace

structure Mixed (A : Type*) [Fintype A] where
  weight : A → ℝ
  nonneg : ∀ a, 0 ≤ weight a
  sum_weight : ∑ a, weight a = 1

namespace Mixed

instance {A : Type*} [Fintype A] : CoeFun (Mixed A) (fun _ => A → ℝ) :=
  ⟨Mixed.weight⟩

lemma weight_nonneg {A : Type*} [Fintype A] (p : Mixed A) (a : A) :
    0 ≤ p a := p.nonneg a

lemma sum_eq_one {A : Type*} [Fintype A] (p : Mixed A) :
    ∑ a, p a = 1 := p.sum_weight

end Mixed

noncomputable def expectedPayoff {A B E : Type*} [Fintype A]
    [AddCommMonoid E] [Module ℝ E]
    (p : Mixed A) (g : A → B → E) (b : B) : E :=
  ∑ a, p a • g a b

noncomputable def gameAverage {A B E : Type*} [Fintype A]
    [AddCommGroup E] [Module ℝ E]
    (g : A → B → E) (strategy : E → Mixed A) (opponent : ℕ → B) : ℕ → E :=
  Approachability.adaptiveAverage
    (fun t y => expectedPayoff (strategy y) g (opponent t))

noncomputable def pureGameAverage {A B E : Type*} [AddCommGroup E]
    [Module ℝ E]
    (g : A → B → E) (strategy : E → A) (opponent : ℕ → B) : ℕ → E :=
  Approachability.adaptiveAverage
    (fun t y => g (strategy y) (opponent t))

noncomputable def closestPoint {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] {C : Set E}
    (hne : C.Nonempty) (hclosed : IsClosed C) (hconvex : Convex ℝ C) : E → E :=
  fun y => Classical.choose
    (Approachability.exists_projection hne hclosed hconvex y)

lemma closestPoint_spec {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] {C : Set E}
    (hne : C.Nonempty) (hclosed : IsClosed C) (hconvex : Convex ℝ C) (y : E) :
    closestPoint hne hclosed hconvex y ∈ C ∧
      ‖y - closestPoint hne hclosed hconvex y‖ = Metric.infDist y C ∧
      ∀ z ∈ C, inner ℝ (y - closestPoint hne hclosed hconvex y)
        (z - closestPoint hne hclosed hconvex y) ≤ 0 := by
  simpa [closestPoint] using
    Classical.choose_spec (Approachability.exists_projection hne hclosed hconvex y)

theorem exists_pointwise_strategy {A B E : Type*} [Fintype A] [Fintype B]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (g : A → B → E) {C : Set E} (hne : C.Nonempty) (hclosed : IsClosed C)
    (hconvex : Convex ℝ C) (Bnd epsilon : ℝ)
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
  exact (Classical.choose_spec (hresponse y) b)

theorem finite_game_approachability_bound
    {A B E : Type*} [Fintype A] [Fintype B]
    [Nonempty B]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (g : A → B → E) (strategy : E → Mixed A) {C : Set E}
    (hne : C.Nonempty) (hclosed : IsClosed C) (hconvex : Convex ℝ C)
    (Bnd epsilon : ℝ)
    (hforce : ∀ y : E, ∀ b : B,
      inner ℝ (y - closestPoint hne hclosed hconvex y)
          (expectedPayoff (strategy y) g b - closestPoint hne hclosed hconvex y) ≤ epsilon)
    (hbound : ∀ y : E, ∀ b : B,
      ‖expectedPayoff (strategy y) g b - closestPoint hne hclosed hconvex y‖ ≤ Bnd)
    (hepsilon : 0 ≤ epsilon) (opponent : ℕ → B) :
    ∀ {T : ℕ}, 0 < T →
      Metric.infDist (gameAverage g strategy opponent T) C ≤
        Real.sqrt (Bnd ^ 2 / T + epsilon) := by
  let avg : ℕ → E := gameAverage g strategy opponent
  let proj : ℕ → E := fun t => closestPoint hne hclosed hconvex (avg t)
  let x : ℕ → E := fun t =>
    expectedPayoff (strategy (avg t)) g (opponent t)
  have hproj : ∀ t : ℕ, proj t ∈ C := by
    intro t
    exact (closestPoint_spec hne hclosed hconvex (avg t)).1
  have hmin : ∀ t : ℕ, ∀ z ∈ C,
      ‖avg t - proj t‖ ≤ ‖avg t - z‖ := by
    intro t z hz
    have hs := closestPoint_spec hne hclosed hconvex (avg t)
    dsimp [proj]
    rw [hs.2.1]
    simpa [dist_eq_norm] using (Metric.infDist_le_dist_of_mem hz :
      Metric.infDist (avg t) C ≤ dist (avg t) z)
  have havg : ∀ t : ℕ, ((t : ℝ) + 1) • avg (t + 1) =
      (t : ℝ) • avg t + x t := by
    intro t
    simpa [avg, gameAverage, x] using
      (Approachability.adaptiveAverage_step
        (fun s y => expectedPayoff (strategy y) g (opponent s)) t)
  have hinner : ∀ t : ℕ,
      inner ℝ (avg t - proj t) (x t - proj t) ≤ epsilon := by
    intro t
    simpa [x, proj] using hforce (avg t) (opponent t)
  have hbound' : ∀ t : ℕ, ‖x t - proj t‖ ≤ Bnd := by
    intro t
    simpa [x, proj] using hbound (avg t) (opponent t)
  intro T hT
  simpa [avg] using
    (Approachability.blackwell_approximate_bound x avg proj Bnd epsilon
      hproj hmin havg hinner hbound' hepsilon (T := T) hT)

theorem finite_game_approachability_of_response
    {A B E : Type*} [Fintype A] [Fintype B]
    [Nonempty B]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (g : A → B → E) {C : Set E}
    (hne : C.Nonempty) (hclosed : IsClosed C) (hconvex : Convex ℝ C)
    (Bnd epsilon : ℝ)
    (hresponse : ∀ y : E, ∃ p : Mixed A, ∀ b : B,
      inner ℝ (y - closestPoint hne hclosed hconvex y)
          (expectedPayoff p g b - closestPoint hne hclosed hconvex y) ≤ epsilon ∧
      ‖expectedPayoff p g b - closestPoint hne hclosed hconvex y‖ ≤ Bnd)
    (hepsilon : 0 ≤ epsilon) :
    ∃ strategy : E → Mixed A, ∀ opponent : ℕ → B, ∀ {T : ℕ}, 0 < T →
      Metric.infDist (gameAverage g strategy opponent T) C ≤
        Real.sqrt (Bnd ^ 2 / T + epsilon) := by
  obtain ⟨strategy, hstrategy⟩ :=
    exists_pointwise_strategy g hne hclosed hconvex Bnd epsilon hresponse
  refine ⟨strategy, ?_⟩
  intro opponent T hT
  apply finite_game_approachability_bound g strategy hne hclosed hconvex
    Bnd epsilon ?_ ?_ hepsilon opponent hT
  · intro y b
    exact (hstrategy y b).1
  · intro y b
    exact (hstrategy y b).2

theorem exists_pure_pointwise_strategy {A B E : Type*} [Fintype A] [Fintype B]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (g : A → B → E) {C : Set E} (hne : C.Nonempty) (hclosed : IsClosed C)
    (hconvex : Convex ℝ C) (Bnd epsilon : ℝ)
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
  exact (Classical.choose_spec (hresponse y) b)

theorem pure_game_approachability_of_response
    {A B E : Type*} [Fintype A] [Fintype B]
    [Nonempty B]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (g : A → B → E) {C : Set E}
    (hne : C.Nonempty) (hclosed : IsClosed C) (hconvex : Convex ℝ C)
    (Bnd epsilon : ℝ)
    (hresponse : ∀ y : E, ∃ a : A, ∀ b : B,
      inner ℝ (y - closestPoint hne hclosed hconvex y)
          (g a b - closestPoint hne hclosed hconvex y) ≤ epsilon ∧
      ‖g a b - closestPoint hne hclosed hconvex y‖ ≤ Bnd)
    (hepsilon : 0 ≤ epsilon) :
    ∃ strategy : E → A, ∀ opponent : ℕ → B, ∀ {T : ℕ}, 0 < T →
      Metric.infDist (pureGameAverage g strategy opponent T) C ≤
        Real.sqrt (Bnd ^ 2 / T + epsilon) := by
  obtain ⟨strategy, hstrategy⟩ :=
    exists_pure_pointwise_strategy g hne hclosed hconvex Bnd epsilon hresponse
  refine ⟨strategy, ?_⟩
  intro opponent T hT
  let avg : ℕ → E := pureGameAverage g strategy opponent
  let proj : ℕ → E := fun t => closestPoint hne hclosed hconvex (avg t)
  let x : ℕ → E := fun t => g (strategy (avg t)) (opponent t)
  have hproj : ∀ t : ℕ, proj t ∈ C := by
    intro t
    exact (closestPoint_spec hne hclosed hconvex (avg t)).1
  have hmin : ∀ t : ℕ, ∀ z ∈ C,
      ‖avg t - proj t‖ ≤ ‖avg t - z‖ := by
    intro t z hz
    have hs := closestPoint_spec hne hclosed hconvex (avg t)
    dsimp [proj]
    rw [hs.2.1]
    simpa [dist_eq_norm] using (Metric.infDist_le_dist_of_mem hz :
      Metric.infDist (avg t) C ≤ dist (avg t) z)
  have havg : ∀ t : ℕ, ((t : ℝ) + 1) • avg (t + 1) =
      (t : ℝ) • avg t + x t := by
    intro t
    simpa [avg, pureGameAverage, x] using
      (Approachability.adaptiveAverage_step
        (fun s y => g (strategy y) (opponent s)) t)
  have hinner : ∀ t : ℕ,
      inner ℝ (avg t - proj t) (x t - proj t) ≤ epsilon := by
    intro t
    simpa [x, proj] using (hstrategy (avg t) (opponent t)).1
  have hbound : ∀ t : ℕ, ‖x t - proj t‖ ≤ Bnd := by
    intro t
    simpa [x, proj] using (hstrategy (avg t) (opponent t)).2
  simpa [avg] using
    (Approachability.blackwell_approximate_bound x avg proj Bnd epsilon
      hproj hmin havg hinner hbound hepsilon (T := T) hT)

end Game
end Blackwell
