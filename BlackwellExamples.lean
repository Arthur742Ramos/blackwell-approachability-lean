import BlackwellSolution

set_option autoImplicit false

/-
# Small checked certificates

These examples exercise the public proof surface on a concrete complete real
inner-product space. They are intentionally certificate-oriented: the
algorithmic half-space condition is explicit, so the examples do not hide a
choice of strategy behind an unverified executable.
-/

namespace Blackwell.Examples

open Blackwell.Palomar

private def zeroSequence : ℕ → ℝ := fun _ => 0
private def zeroTarget : Set ℝ := {0}
private def zeroProjection : ℕ → ℝ := fun _ => 0

lemma zero_certificate :
    Metric.infDist (Blackwell.Approachability.runningAverage zeroSequence 8)
        zeroTarget ≤ 0 / Real.sqrt 8 := by
  have hbound : ∀ t : ℕ,
      ‖zeroSequence t - zeroProjection t‖ ≤ (0 : ℝ) := by
    intro t
    simp [zeroSequence, zeroProjection]
  have hproj : ∀ t : ℕ, zeroProjection t ∈ zeroTarget := by
    intro t
    simp [zeroProjection, zeroTarget]
  have hmin : ∀ t : ℕ, ∀ z ∈ zeroTarget,
      ‖Blackwell.Approachability.runningAverage zeroSequence t -
          zeroProjection t‖ ≤
        ‖Blackwell.Approachability.runningAverage zeroSequence t - z‖ := by
    intro t z hz
    simp [zeroSequence, zeroProjection,
      Blackwell.Approachability.runningAverage, zeroTarget] at *
  have havg : ∀ t : ℕ,
      ((t : ℝ) + 1) •
          Blackwell.Approachability.runningAverage zeroSequence (t + 1) =
        (t : ℝ) • Blackwell.Approachability.runningAverage zeroSequence t +
          zeroSequence t := by
    intro t
    exact Blackwell.Approachability.runningAverage_step zeroSequence t
  have hinner : ∀ t : ℕ,
      inner ℝ
          (Blackwell.Approachability.runningAverage zeroSequence t -
            zeroProjection t)
          (zeroSequence t - zeroProjection t) ≤ 0 := by
    intro t
    simp [zeroSequence, zeroProjection]
  exact blackwell_approachability_bound zeroSequence
    (Blackwell.Approachability.runningAverage zeroSequence) zeroProjection 0
    hproj hmin havg hinner hbound (by norm_num) (by norm_num)

end Blackwell.Examples
