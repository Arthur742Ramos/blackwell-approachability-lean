import BlackwellSolution
import BlackwellReduction

set_option autoImplicit false

namespace Blackwell.SubstantiveExamples

open scoped BigOperators RealInnerProductSpace
open Blackwell.Palomar

private def intervalTarget : Set ℝ := Set.Icc (0 : ℝ) 1

private def purePayoff (a : Bool) (_b : Bool) : ℝ :=
  if a then 1 else 0

private def positiveResponse (_y : ℝ) : Bool := true

lemma interval_response_condition :
    ∀ y : ℝ, ∃ a : Bool, ∀ b : Bool,
      inner ℝ (y - closestPoint (C := intervalTarget)
          (by exact ⟨0, by simp [intervalTarget]⟩)
          (by exact isClosed_Icc) (by exact convex_Icc 0 1) y)
          (purePayoff a b - closestPoint (C := intervalTarget)
            (by exact ⟨0, by simp [intervalTarget]⟩)
            (by exact isClosed_Icc) (by exact convex_Icc 0 1) y) ≤ 0 ∧
      ‖purePayoff a b - closestPoint (C := intervalTarget)
        (by exact ⟨0, by simp [intervalTarget]⟩)
        (by exact isClosed_Icc) (by exact convex_Icc 0 1) y‖ ≤ 1 := by
  intro y
  let hne : intervalTarget.Nonempty := ⟨0, by simp [intervalTarget]⟩
  let hclosed : IsClosed intervalTarget := isClosed_Icc
  let hconvex : Convex ℝ intervalTarget := convex_Icc 0 1
  refine ⟨positiveResponse y, ?_⟩
  intro b
  have hp := (closestPoint_spec hne hclosed hconvex y).1
  have hp' : 0 ≤ closestPoint hne hclosed hconvex y ∧
      closestPoint hne hclosed hconvex y ≤ 1 := by
    simpa [intervalTarget] using hp
  have hnormal := (closestPoint_spec hne hclosed hconvex y).2.2
    (1 : ℝ) (by simp [intervalTarget])
  have hpayoff : purePayoff (positiveResponse y) b = 1 := by
    simp [positiveResponse, purePayoff]
  have hbound : ‖(1 : ℝ) - closestPoint hne hclosed hconvex y‖ ≤ 1 := by
    have hnonneg : 0 ≤ (1 : ℝ) - closestPoint hne hclosed hconvex y := by
      linarith [hp'.2]
    rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
    linarith [hp'.1]
  rw [hpayoff]
  exact ⟨by simpa using hnormal, by simpa using hbound⟩

lemma pure_game_convergence :
    ∃ strategy : ℝ → Bool, ∀ opponent : ℕ → Bool, ∀ {T : ℕ}, 0 < T →
      Metric.infDist
          (gameAverage purePayoff strategy opponent T) intervalTarget ≤
        Real.sqrt (1 / T) := by
  let hne : intervalTarget.Nonempty := ⟨0, by simp [intervalTarget]⟩
  let hclosed : IsClosed intervalTarget := isClosed_Icc
  let hconvex : Convex ℝ intervalTarget := convex_Icc 0 1
  have hresponse : ∀ y : ℝ, ∃ a : Bool, ∀ b : Bool,
      inner ℝ (y - closestPoint hne hclosed hconvex y)
          (purePayoff a b - closestPoint hne hclosed hconvex y) ≤ 0 ∧
      ‖purePayoff a b - closestPoint hne hclosed hconvex y‖ ≤ 1 := by
    intro y
    exact interval_response_condition y
  simpa using (pure_game_approachability_of_response purePayoff hne hclosed
    hconvex 1 0 hresponse (by norm_num) (by norm_num))

private def constantLoss (_t : ℕ) (_a : Bool) : ℝ := 1
private def constantAction (_t : ℕ) : Bool := false

lemma regret_conversion_is_dimension_sensitive :
    Reduction.l2Norm (fun _ : Bool => (1 : ℝ)) = Real.sqrt (Fintype.card Bool) := by
  simpa using (Reduction.dimension_factor_is_attained (A := Bool) 1 (by norm_num))

lemma regret_coordinates_follow_from_euclidean_certificate
    (T : ℕ) (delta : ℝ)
    (hdelta : Reduction.l2Norm
      (Reduction.averageRegret constantLoss constantAction T) ≤ delta) :
    ∀ a : Bool,
      Reduction.averageRegret constantLoss constantAction T a ≤ delta := by
  exact Reduction.regret_coordinate_of_l2_bound
    constantLoss constantAction T delta hdelta

end Blackwell.SubstantiveExamples
