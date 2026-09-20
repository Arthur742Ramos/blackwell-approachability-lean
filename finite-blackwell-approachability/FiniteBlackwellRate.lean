import FiniteBlackwell
import ApproachabilityCore

set_option autoImplicit false

namespace Blackwell.FiniteApproachability

open Set
open scoped BigOperators RealInnerProductSpace

/-- Expected running payoff against an arbitrary pure opponent sequence. -/
noncomputable def gameAverage {A B E : Type*} [Fintype A]
    [AddCommGroup E] [Module ℝ E]
    (g : A → B → E) (strategy : E → Mixed A) (opponent : ℕ → B) : ℕ → E :=
  Approachability.adaptiveAverage (fun t y =>
    expectedPayoff (strategy y).1 g (opponent t))

/-- A pointwise forcing response with bounded displacement yields the game rate. -/
theorem finite_game_approachability_bound
    {A B E : Type*} [Fintype A] [Fintype B] [Nonempty A] [Nonempty B]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (g : A → B → E) (strategy : E → Mixed A) {C : Set E}
    (hne : C.Nonempty) (hclosed : IsClosed C) (hconvex : Convex ℝ C)
    (Bnd : ℝ)
    (hforce : ∀ y : E, ∀ b : B,
      inner ℝ (y - closestPoint hne hclosed hconvex y)
        (expectedPayoff (strategy y).1 g b - closestPoint hne hclosed hconvex y) ≤ 0)
    (hbound : ∀ y : E, ∀ b : B,
      ‖expectedPayoff (strategy y).1 g b - closestPoint hne hclosed hconvex y‖ ≤ Bnd)
    (hBnd : 0 ≤ Bnd) (opponent : ℕ → B) :
    ∀ {T : ℕ}, 0 < T →
      Metric.infDist (gameAverage g strategy opponent T) C ≤ Bnd / Real.sqrt T := by
  let avg : ℕ → E := gameAverage g strategy opponent
  let proj : ℕ → E := fun t => closestPoint hne hclosed hconvex (avg t)
  let x : ℕ → E := fun t =>
    expectedPayoff (strategy (avg t)).1 g (opponent t)
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
        (fun s y => expectedPayoff (strategy y).1 g (opponent s)) t)
  have hinner : ∀ t : ℕ,
      inner ℝ (avg t - proj t) (x t - proj t) ≤ 0 := by
    intro t
    simpa [x, proj] using hforce (avg t) (opponent t)
  have hbound' : ∀ t : ℕ, ‖x t - proj t‖ ≤ Bnd := by
    intro t
    simpa [x, proj] using hbound (avg t) (opponent t)
  intro T hT
  simpa [avg] using
    (Approachability.blackwell_approachability_bound x avg proj Bnd
      hproj hmin havg hinner hbound' hBnd (T := T) hT)

/-- A response oracle yields one causal strategy with the stated finite-time rate. -/
theorem finite_game_approachability_of_response
    {A B E : Type*} [Fintype A] [Fintype B] [Nonempty A] [Nonempty B]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (g : A → B → E) {C : Set E}
    (hne : C.Nonempty) (hclosed : IsClosed C) (hconvex : Convex ℝ C)
    (Bnd : ℝ)
    (hresponse : ∀ y : E, ∃ p : Mixed A, ∀ b : B,
      inner ℝ (y - closestPoint hne hclosed hconvex y)
        (expectedPayoff p.1 g b - closestPoint hne hclosed hconvex y) ≤ 0 ∧
      ‖expectedPayoff p.1 g b - closestPoint hne hclosed hconvex y‖ ≤ Bnd)
    (hBnd : 0 ≤ Bnd) :
    ∃ strategy : E → Mixed A, ∀ opponent : ℕ → B, ∀ {T : ℕ}, 0 < T →
      Metric.infDist (gameAverage g strategy opponent T) C ≤ Bnd / Real.sqrt T := by
  classical
  let strategy : E → Mixed A := fun y => Classical.choose (hresponse y)
  refine ⟨strategy, ?_⟩
  intro opponent T hT
  apply finite_game_approachability_bound g strategy hne hclosed hconvex
    Bnd ?_ ?_ hBnd opponent hT
  · intro y b
    exact (Classical.choose_spec (hresponse y) b).1
  · intro y b
    exact (Classical.choose_spec (hresponse y) b).2

/--
The finite game theorem from a mixed Blackwell condition.

The player's action may be mixed and may depend on the expected running
payoff. For every pure opponent sequence, the expected average payoff is
within `(G + R) / sqrt T` of the target after `T > 0` rounds. The condition
is stated against every mixed opponent action; Sion minimax supplies one
response that works against all pure opponent actions, while the payoff and
target radii give the uniform displacement bound.
-/
theorem finite_game_approachability_of_mixedBlackwell
    {A B E : Type*} [Fintype A] [Fintype B] [Nonempty A] [Nonempty B]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (g : A → B → E) {C : Set E}
    (hne : C.Nonempty) (hclosed : IsClosed C) (hconvex : Convex ℝ C)
    (G R : ℝ) (hG : 0 ≤ G) (hR : 0 ≤ R)
    (hpay : ∀ a b, ‖g a b‖ ≤ G)
    (hradius : ∀ z ∈ C, ‖z‖ ≤ R)
    (hblackwell : mixedBlackwellCondition g hne hclosed hconvex) :
    ∃ strategy : E → Mixed A, ∀ opponent : ℕ → B, ∀ {T : ℕ}, 0 < T →
      Metric.infDist (gameAverage g strategy opponent T) C ≤ (G + R) / Real.sqrt T := by
  have hresponse : ∀ y : E, ∃ p : Mixed A, ∀ b : B,
      inner ℝ (y - closestPoint hne hclosed hconvex y)
        (expectedPayoff p.1 g b - closestPoint hne hclosed hconvex y) ≤ 0 ∧
      ‖expectedPayoff p.1 g b - closestPoint hne hclosed hconvex y‖ ≤ G + R := by
    intro y
    let z := closestPoint hne hclosed hconvex y
    have hfeasible : ∀ q : B → ℝ, q ∈ simplexSet B →
        ∃ p : A → ℝ, p ∈ simplexSet A ∧
          normalScore g y z p q ≤ inner ℝ (y - z) z := by
      simpa [z] using hblackwell y
    obtain ⟨p, hp, huniform⟩ := exists_uniform_mixed_response g y z hfeasible
    have hpSimplex : simplex p := hp
    refine ⟨⟨p, hpSimplex⟩, ?_⟩
    intro b
    have hscore := huniform (pointMass b) (pointMass_mem_simplexSet b)
    have hscore' : inner ℝ (y - z) (expectedPayoff p g b) ≤
        inner ℝ (y - z) z := by
      simpa [normalScore, mixedExpectedPayoff_pointMass] using hscore
    have hforce : inner ℝ (y - z) (expectedPayoff p g b - z) ≤ 0 := by
      rw [inner_sub_right]
      linarith
    have hz : z ∈ C := (closestPoint_spec hne hclosed hconvex y).1
    have hnorm : ‖expectedPayoff p g b - z‖ ≤ G + R := by
      calc
        ‖expectedPayoff p g b - z‖ ≤
            ‖expectedPayoff p g b‖ + ‖z‖ := norm_sub_le _ _
        _ ≤ G + R := add_le_add
          (expectedPayoff_norm_le p hpSimplex g b G (fun a => hpay a b))
          (hradius z hz)
    exact ⟨hforce, hnorm⟩
  exact finite_game_approachability_of_response g hne hclosed hconvex
    (G + R) hresponse (add_nonneg hG hR)

end Blackwell.FiniteApproachability
