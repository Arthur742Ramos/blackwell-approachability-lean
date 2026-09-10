import BlackwellApproachability

set_option autoImplicit false

/-
# Small checked certificates

These examples exercise the public proof surface on a concrete complete real
inner-product space. They are intentionally certificate-oriented: the
algorithmic half-space condition is explicit, so the examples do not hide a
choice of strategy behind an unverified executable.
-/

namespace Blackwell.Examples


private def zeroSequence : ℕ → ℝ := fun _ => 0
private def zeroTarget : Set ℝ := {0}
private def zeroProjection : ℕ → ℝ := fun _ => 0

private def cancellationSequence : ℕ → ℝ
  | 0 => 1
  | 1 => -1
  | _ => 0

private def cancellationTarget : Set ℝ := {0}
private def cancellationProjection : ℕ → ℝ := fun _ => 0

private noncomputable def signResponse (y : ℝ) : ℝ := if 0 < y then -1 else 1
private def signProjection (_y : ℝ) : ℝ := 0

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
  exact Blackwell.Approachability.blackwell_approachability_bound zeroSequence
    (Blackwell.Approachability.runningAverage zeroSequence) zeroProjection 0
    hproj hmin havg hinner hbound (by norm_num) (by norm_num)

lemma cancellation_starts_outside_target :
    Blackwell.Approachability.runningAverage cancellationSequence 1 = 1 ∧
      (1 : ℝ) ∉ cancellationTarget := by
  constructor
  · norm_num [cancellationSequence, Blackwell.Approachability.runningAverage]
  · simp [cancellationTarget]

lemma cancellation_certificate :
    Metric.infDist
        (Blackwell.Approachability.runningAverage cancellationSequence 2)
        cancellationTarget ≤ (1 : ℝ) / Real.sqrt 2 := by
  have hbound : ∀ t : ℕ,
      ‖cancellationSequence t - cancellationProjection t‖ ≤ (1 : ℝ) := by
    intro t
    cases t with
    | zero => norm_num [cancellationSequence, cancellationProjection]
    | succ t =>
        cases t with
        | zero => norm_num [cancellationSequence, cancellationProjection]
        | succ t => simp [cancellationSequence, cancellationProjection]
  have hproj : ∀ t : ℕ, cancellationProjection t ∈ cancellationTarget := by
    intro t
    simp [cancellationProjection, cancellationTarget]
  have hmin : ∀ t : ℕ, ∀ z ∈ cancellationTarget,
      ‖Blackwell.Approachability.runningAverage cancellationSequence t -
          cancellationProjection t‖ ≤
        ‖Blackwell.Approachability.runningAverage cancellationSequence t - z‖ := by
    intro t z hz
    have hz0 : z = 0 := by simpa [cancellationTarget] using hz
    subst z
    simp [cancellationProjection]
  have havg : ∀ t : ℕ,
      ((t : ℝ) + 1) •
          Blackwell.Approachability.runningAverage cancellationSequence (t + 1) =
        (t : ℝ) • Blackwell.Approachability.runningAverage cancellationSequence t +
          cancellationSequence t := by
    intro t
    exact Blackwell.Approachability.runningAverage_step cancellationSequence t
  have hinner : ∀ t : ℕ,
      inner ℝ
          (Blackwell.Approachability.runningAverage cancellationSequence t -
            cancellationProjection t)
          (cancellationSequence t - cancellationProjection t) ≤ 0 := by
    intro t
    cases t with
    | zero => simp [cancellationSequence, cancellationProjection,
        Blackwell.Approachability.runningAverage]
    | succ t =>
        cases t with
        | zero => norm_num [cancellationSequence, cancellationProjection,
            Blackwell.Approachability.runningAverage]
        | succ t => simp [cancellationSequence, cancellationProjection]
  exact Blackwell.Approachability.blackwell_approachability_bound cancellationSequence
    (Blackwell.Approachability.runningAverage cancellationSequence)
    cancellationProjection 1 hproj hmin havg hinner hbound (by norm_num)
    (by norm_num)

lemma response_oracle_certificate :
    Metric.infDist
        (Blackwell.Approachability.responseAverage signResponse 2)
        cancellationTarget ≤ (1 : ℝ) / Real.sqrt 2 := by
  have hproj : ∀ y : ℝ, signProjection y ∈ cancellationTarget := by
    intro y
    simp [signProjection, cancellationTarget]
  have hmin : ∀ y : ℝ, ∀ z ∈ cancellationTarget,
      ‖y - signProjection y‖ ≤ ‖y - z‖ := by
    intro y z hz
    have hz0 : z = 0 := by simpa [cancellationTarget] using hz
    subst z
    simp [signProjection]
  have hinner : ∀ y : ℝ,
      inner ℝ (y - signProjection y)
        (signResponse y - signProjection y) ≤ 0 := by
    intro y
    by_cases hy : 0 < y
    · simp [signResponse, signProjection, hy]
      linarith
    · by_cases hy0 : y = 0
      · subst y
        simp [signResponse, signProjection]
      · have hy' : y < 0 := lt_of_le_of_ne (le_of_not_gt hy) hy0
        simp [signResponse, signProjection, hy]
        linarith
  have hbound : ∀ y : ℝ,
      ‖signResponse y - signProjection y‖ ≤ (1 : ℝ) := by
    intro y
    by_cases hy : 0 < y <;> simp [signResponse, signProjection, hy]
  exact Blackwell.Approachability.blackwell_response_bound signResponse
    signProjection 1 hproj hmin hinner hbound (by norm_num) (by norm_num)

end Blackwell.Examples
