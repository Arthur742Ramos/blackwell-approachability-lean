import BlackwellApproachability

set_option autoImplicit false

/-
# Proof surface

The selected declarations mirror BlackwellChallenge.lean exactly. Their
proofs are short adapters to the independently named implementation facts.
-/

namespace Blackwell.Palomar

theorem blackwell_approachability_bound {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {C : Set E} (x avg proj : ℕ → E) (B : ℝ)
    (hproj : ∀ t : ℕ, proj t ∈ C)
    (hmin : ∀ t : ℕ, ∀ z ∈ C,
      ‖avg t - proj t‖ ≤ ‖avg t - z‖)
    (havg : ∀ t : ℕ, ((t : ℝ) + 1) • avg (t + 1) =
      (t : ℝ) • avg t + x t)
    (hinner : ∀ t : ℕ,
      inner ℝ (avg t - proj t) (x t - proj t) ≤ 0)
    (hbound : ∀ t : ℕ, ‖x t - proj t‖ ≤ B) (hB : 0 ≤ B) :
    ∀ {T : ℕ}, 0 < T →
      Metric.infDist (avg T) C ≤ B / Real.sqrt T := by
  exact Blackwell.Approachability.blackwell_approachability_bound
    x avg proj B hproj hmin havg hinner hbound hB

theorem exists_projection {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] {C : Set E}
    (hne : C.Nonempty) (hclosed : IsClosed C) (hconvex : Convex ℝ C)
    (y : E) :
    ∃ p ∈ C, ‖y - p‖ = Metric.infDist y C ∧
      ∀ z ∈ C, inner ℝ (y - p) (z - p) ≤ 0 := by
  exact Blackwell.Approachability.exists_projection hne hclosed hconvex y

end Blackwell.Palomar

