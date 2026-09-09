import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Tactic

set_option autoImplicit false

/-
# Independent statement surface

The Challenge module intentionally imports only Mathlib. It states the
conditional geometric certificate and the closest-point theorem without
importing the implementation. The first result assumes the usual
supporting-half-space condition; it does not claim existence of a strategic
response producing that condition. The proof placeholders are the mechanical
comparison targets; the checked proofs live in BlackwellSolution.lean and
BlackwellApproachability.lean.
-/

namespace Blackwell.Palomar

/-- A conditional finite-time distance bound from the Blackwell
    supporting-half-space certificate. -/
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
  sorry

/-- A closest point to `y` in a nonempty closed convex target, together with
    the normal-cone inequality for every target point. -/
theorem exists_projection {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] {C : Set E}
    (hne : C.Nonempty) (hclosed : IsClosed C) (hconvex : Convex ℝ C)
    (y : E) :
    ∃ p ∈ C, ‖y - p‖ = Metric.infDist y C ∧
      ∀ z ∈ C, inner ℝ (y - p) (z - p) ≤ 0 := by
  sorry

end Blackwell.Palomar
