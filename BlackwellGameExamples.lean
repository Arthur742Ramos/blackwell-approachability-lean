import BlackwellGame

set_option autoImplicit false

namespace Blackwell.GameExamples

open scoped BigOperators RealInnerProductSpace
open Blackwell.Game

private noncomputable def fair : Mixed Bool where
  weight := fun _ => (1 / 2 : ℝ)
  nonneg := by intro b; norm_num
  sum_weight := by simp

private def matchingPayoff (a b : Bool) : ℝ :=
  if a = b then 1 else -1

private def singletonTarget : Set ℝ := {0}

lemma fair_payoff (b : Bool) :
    expectedPayoff fair matchingPayoff b = 0 := by
  cases b <;> simp [expectedPayoff, fair, matchingPayoff]

lemma finite_game_strategy_exists :
    ∃ strategy : ℝ → Mixed Bool, ∀ y : ℝ, ∀ b : Bool,
      inner ℝ (y - Blackwell.Game.closestPoint
          (C := singletonTarget) (by simp [singletonTarget])
          isClosed_singleton (convex_singleton 0) y)
          (expectedPayoff (strategy y) matchingPayoff b -
            Blackwell.Game.closestPoint
              (C := singletonTarget) (by simp [singletonTarget])
              isClosed_singleton (convex_singleton 0) y) ≤ 0 ∧
      ‖expectedPayoff (strategy y) matchingPayoff b -
        Blackwell.Game.closestPoint
          (C := singletonTarget) (by simp [singletonTarget])
          isClosed_singleton (convex_singleton 0) y‖ ≤ 1 := by
  let hne : singletonTarget.Nonempty := by simp [singletonTarget]
  let hclosed : IsClosed singletonTarget := isClosed_singleton
  let hconvex : Convex ℝ singletonTarget := convex_singleton 0
  have hresponse : ∀ y : ℝ, ∃ p : Mixed Bool, ∀ b : Bool,
      inner ℝ (y - closestPoint hne hclosed hconvex y)
          (expectedPayoff p matchingPayoff b - closestPoint hne hclosed hconvex y) ≤ 0 ∧
      ‖expectedPayoff p matchingPayoff b - closestPoint hne hclosed hconvex y‖ ≤ 1 := by
    intro y
    refine ⟨fair, ?_⟩
    intro b
    have hp : closestPoint hne hclosed hconvex y = 0 := by
      have hs := (closestPoint_spec hne hclosed hconvex y).1
      simpa [singletonTarget] using hs
    rw [fair_payoff, hp]
    simp
  obtain ⟨strategy, hstrategy⟩ :=
    exists_pointwise_strategy matchingPayoff hne hclosed hconvex 1 0 hresponse
  refine ⟨strategy, ?_⟩
  simpa [hne, hclosed, hconvex, singletonTarget] using hstrategy

lemma finite_game_converges :
    ∃ strategy : ℝ → Mixed Bool, ∀ opponent : ℕ → Bool, ∀ {T : ℕ}, 0 < T →
      Metric.infDist
          (gameAverage matchingPayoff strategy opponent T) singletonTarget ≤
        Real.sqrt (1 / T) := by
  let hne : singletonTarget.Nonempty := by simp [singletonTarget]
  let hclosed : IsClosed singletonTarget := isClosed_singleton
  let hconvex : Convex ℝ singletonTarget := convex_singleton 0
  have hresponse : ∀ y : ℝ, ∃ p : Mixed Bool, ∀ b : Bool,
      inner ℝ (y - closestPoint hne hclosed hconvex y)
          (expectedPayoff p matchingPayoff b - closestPoint hne hclosed hconvex y) ≤ 0 ∧
      ‖expectedPayoff p matchingPayoff b - closestPoint hne hclosed hconvex y‖ ≤ 1 := by
    intro y
    refine ⟨fair, ?_⟩
    intro b
    have hp : closestPoint hne hclosed hconvex y = 0 := by
      have hs := (closestPoint_spec hne hclosed hconvex y).1
      simpa [singletonTarget] using hs
    rw [fair_payoff, hp]
    simp
  simpa using (finite_game_approachability_of_response matchingPayoff hne hclosed hconvex
    1 0 hresponse (by norm_num))

end Blackwell.GameExamples
