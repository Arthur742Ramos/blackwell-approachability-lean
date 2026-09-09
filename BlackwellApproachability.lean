import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Tactic

set_option autoImplicit false

/-
# Blackwell approachability certificate

This file proves the conditional quantitative Euclidean step in Blackwell's
approachability argument. A witness proj t is supplied for each running
average. It lies in the target, minimizes the distance to that average, and
the next payoff lies in the corresponding Blackwell half-space. If the
witness-relative payoff displacement is bounded by B, the distance of the Tth
average to the target is at most B / sqrt T. The file does not construct the
payoff sequence or prove the strategic-game response condition needed to
establish those hypotheses.

The proof is deliberately separated into three reusable pieces:

* norm_affine_sq_le expands one Blackwell step in a real inner-product space;
* blackwell_approachability_bound telescopes the resulting squared-distance
  recurrence; and
* exists_projection obtains the closest-point witness and its normal-cone
  inequality for every nonempty closed convex target; and
* blackwell_response_bound applies the certificate to an explicit online
  response oracle.

The target need not be a subspace, and the result does not assume a finite
dimension. Completeness is used only for the projection-existence theorem.
-/

namespace Blackwell
namespace Approachability

open scoped RealInnerProductSpace

lemma norm_affine_sq_le {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (r : ℝ) (a b : E) (B : ℝ)
    (hr : 0 ≤ r) (hr' : r ≤ 1) (hinner : inner ℝ a b ≤ 0)
    (hb : ‖b‖ ≤ B) :
    ‖r • a + (1 - r) • b‖ ^ 2 ≤
      r ^ 2 * ‖a‖ ^ 2 + (1 - r) ^ 2 * B ^ 2 := by
  rw [norm_add_sq_real, norm_smul, norm_smul, real_inner_smul_left,
    real_inner_smul_right]
  have h1 : 0 ≤ 1 - r := by linarith
  have hrnorm : ‖r‖ = r := by
    rw [Real.norm_eq_abs, abs_of_nonneg hr]
  have h1norm : ‖1 - r‖ = 1 - r := by
    rw [Real.norm_eq_abs, abs_of_nonneg h1]
  rw [hrnorm, h1norm]
  have hmul : r * (1 - r) * inner ℝ a b ≤ 0 := by
    exact mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hr h1) hinner
  have hcross : 2 * (r * (1 - r) * inner ℝ a b) ≤ 0 := by
    nlinarith
  have hbnorm : ‖b‖ ^ 2 ≤ B ^ 2 := by
    nlinarith [norm_nonneg b]
  nlinarith

lemma norm_affine_sq_le_error {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (r : ℝ) (a b : E) (B epsilon : ℝ)
    (hr : 0 ≤ r) (hr' : r ≤ 1) (hinner : inner ℝ a b ≤ epsilon)
    (hb : ‖b‖ ≤ B) :
    ‖r • a + (1 - r) • b‖ ^ 2 ≤
      r ^ 2 * ‖a‖ ^ 2 + (1 - r) ^ 2 * B ^ 2 +
        2 * r * (1 - r) * epsilon := by
  rw [norm_add_sq_real, norm_smul, norm_smul, real_inner_smul_left,
    real_inner_smul_right]
  have h1 : 0 ≤ 1 - r := by linarith
  have hrnorm : ‖r‖ = r := by
    rw [Real.norm_eq_abs, abs_of_nonneg hr]
  have h1norm : ‖1 - r‖ = 1 - r := by
    rw [Real.norm_eq_abs, abs_of_nonneg h1]
  rw [hrnorm, h1norm]
  have hcross : 2 * (r * (1 - r) * inner ℝ a b) ≤
      2 * (r * (1 - r) * epsilon) := by
    have hmul : 0 ≤ r * (1 - r) := mul_nonneg hr h1
    nlinarith
  have hbnorm : ‖b‖ ^ 2 ≤ B ^ 2 := by
    nlinarith [norm_nonneg b]
  nlinarith

lemma blackwell_step_sq {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {C : Set E} (x avg proj : ℕ → E) (B : ℝ)
    (t : ℕ) (hproj : ∀ s : ℕ, proj s ∈ C)
    (hmin : ∀ s : ℕ, ∀ z ∈ C,
      ‖avg s - proj s‖ ≤ ‖avg s - z‖)
    (havg : ((t : ℝ) + 1) • avg (t + 1) =
      (t : ℝ) • avg t + x t)
    (hinner : inner ℝ (avg t - proj t) (x t - proj t) ≤ 0)
    (hbound : ‖x t - proj t‖ ≤ B) :
    ((t : ℝ) + 1) ^ 2 * ‖avg (t + 1) - proj (t + 1)‖ ^ 2 ≤
      (t : ℝ) ^ 2 * ‖avg t - proj t‖ ^ 2 + B ^ 2 := by
  have ht : 0 ≤ (t : ℝ) := by positivity
  have ht1 : 0 < (t : ℝ) + 1 := by positivity
  have ht1ne : (t : ℝ) + 1 ≠ 0 := ne_of_gt ht1
  let r : ℝ := (t : ℝ) / ((t : ℝ) + 1)
  have hr : 0 ≤ r := by
    dsimp [r]
    positivity
  have hr' : r ≤ 1 := by
    dsimp [r]
    rw [div_le_iff₀ ht1]
    linarith
  have h1r : 1 - r = 1 / ((t : ℝ) + 1) := by
    dsimp [r]
    field_simp
    ring
  have hvec : avg (t + 1) - proj t =
      r • (avg t - proj t) + (1 - r) • (x t - proj t) := by
    rw [h1r]
    dsimp [r]
    apply (smul_right_injective E ht1ne)
    change ((t : ℝ) + 1) • (avg (t + 1) - proj t) =
      ((t : ℝ) + 1) • (((t : ℝ) / ((t : ℝ) + 1)) •
        (avg t - proj t) + (1 / ((t : ℝ) + 1)) •
        (x t - proj t))
    rw [smul_sub, smul_add, smul_smul, smul_smul, havg]
    field_simp
    module
  have hsq := norm_affine_sq_le r (avg t - proj t) (x t - proj t) B
    hr hr' hinner hbound
  rw [← hvec] at hsq
  have hnext : ‖avg (t + 1) - proj (t + 1)‖ ≤
      ‖avg (t + 1) - proj t‖ :=
    hmin (t + 1) (proj t) (hproj t)
  have hsqnext : ‖avg (t + 1) - proj (t + 1)‖ ^ 2 ≤
      ‖avg (t + 1) - proj t‖ ^ 2 := by
    nlinarith [norm_nonneg (avg (t + 1) - proj (t + 1)),
      norm_nonneg (avg (t + 1) - proj t)]
  have hsq' : ‖avg (t + 1) - proj (t + 1)‖ ^ 2 ≤
      r ^ 2 * ‖avg t - proj t‖ ^ 2 + (1 - r) ^ 2 * B ^ 2 :=
    hsqnext.trans hsq
  rw [h1r] at hsq'
  dsimp [r] at hsq'
  have hmul := mul_le_mul_of_nonneg_left hsq' (sq_nonneg ((t : ℝ) + 1))
  field_simp [ht1ne] at hmul
  nlinarith

lemma blackwell_step_sq_error {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {C : Set E} (x avg proj : ℕ → E)
    (B epsilon : ℝ) (t : ℕ) (hproj : ∀ s : ℕ, proj s ∈ C)
    (hmin : ∀ s : ℕ, ∀ z ∈ C,
      ‖avg s - proj s‖ ≤ ‖avg s - z‖)
    (havg : ((t : ℝ) + 1) • avg (t + 1) =
      (t : ℝ) • avg t + x t)
    (hinner : inner ℝ (avg t - proj t) (x t - proj t) ≤ epsilon)
    (hbound : ‖x t - proj t‖ ≤ B) :
    ((t : ℝ) + 1) ^ 2 * ‖avg (t + 1) - proj (t + 1)‖ ^ 2 ≤
      (t : ℝ) ^ 2 * ‖avg t - proj t‖ ^ 2 + B ^ 2 +
        2 * (t : ℝ) * epsilon := by
  have ht : 0 ≤ (t : ℝ) := by positivity
  have ht1 : 0 < (t : ℝ) + 1 := by positivity
  have ht1ne : (t : ℝ) + 1 ≠ 0 := ne_of_gt ht1
  let r : ℝ := (t : ℝ) / ((t : ℝ) + 1)
  have hr : 0 ≤ r := by
    dsimp [r]
    positivity
  have hr' : r ≤ 1 := by
    dsimp [r]
    rw [div_le_iff₀ ht1]
    linarith
  have h1r : 1 - r = 1 / ((t : ℝ) + 1) := by
    dsimp [r]
    field_simp
    ring
  have hvec : avg (t + 1) - proj t =
      r • (avg t - proj t) + (1 - r) • (x t - proj t) := by
    rw [h1r]
    dsimp [r]
    apply (smul_right_injective E ht1ne)
    change ((t : ℝ) + 1) • (avg (t + 1) - proj t) =
      ((t : ℝ) + 1) • (((t : ℝ) / ((t : ℝ) + 1)) •
        (avg t - proj t) + (1 / ((t : ℝ) + 1)) •
        (x t - proj t))
    rw [smul_sub, smul_add, smul_smul, smul_smul, havg]
    field_simp
    module
  have hsq := norm_affine_sq_le_error r (avg t - proj t) (x t - proj t)
    B epsilon hr hr' hinner hbound
  rw [← hvec] at hsq
  have hnext : ‖avg (t + 1) - proj (t + 1)‖ ≤
      ‖avg (t + 1) - proj t‖ :=
    hmin (t + 1) (proj t) (hproj t)
  have hsqnext : ‖avg (t + 1) - proj (t + 1)‖ ^ 2 ≤
      ‖avg (t + 1) - proj t‖ ^ 2 := by
    nlinarith [norm_nonneg (avg (t + 1) - proj (t + 1)),
      norm_nonneg (avg (t + 1) - proj t)]
  have hsq' : ‖avg (t + 1) - proj (t + 1)‖ ^ 2 ≤
      r ^ 2 * ‖avg t - proj t‖ ^ 2 + (1 - r) ^ 2 * B ^ 2 +
        2 * r * (1 - r) * epsilon := hsqnext.trans hsq
  rw [h1r] at hsq'
  dsimp [r] at hsq'
  have hmul := mul_le_mul_of_nonneg_left hsq' (sq_nonneg ((t : ℝ) + 1))
  field_simp [ht1ne] at hmul
  nlinarith

/-- Quantitative Blackwell approachability from the half-space certificate. -/
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
  intro T hT
  let err : ℕ → ℝ := fun t => ‖avg t - proj t‖
  have henergy : ∀ t : ℕ, (t : ℝ) ^ 2 * err t ^ 2 ≤
      (t : ℝ) * B ^ 2 := by
    intro t
    induction t with
    | zero => simp
    | succ t ih =>
        have hstep := blackwell_step_sq x avg proj B t hproj hmin
          (havg t) (hinner t) (hbound t)
        dsimp [err] at ih ⊢
        simpa [Nat.cast_succ] using (show
          ((t : ℝ) + 1) ^ 2 *
              ‖avg (t + 1) - proj (t + 1)‖ ^ 2 ≤
            ((t : ℝ) + 1) * B ^ 2 by
          nlinarith [hstep, ih])
  have hTreal : 0 < (T : ℝ) := by exact_mod_cast hT
  have hdivide : (T : ℝ) * err T ^ 2 ≤ B ^ 2 := by
    apply le_of_mul_le_mul_left _ hTreal
    calc
      (T : ℝ) * ((T : ℝ) * err T ^ 2) =
          (T : ℝ) ^ 2 * err T ^ 2 := by ring
      _ ≤ (T : ℝ) * B ^ 2 := henergy T
  have hdiv : err T ^ 2 ≤ B ^ 2 / (T : ℝ) := by
    apply (le_div_iff₀ hTreal).2
    simpa [mul_comm] using hdivide
  have hsqrt : 0 < Real.sqrt (T : ℝ) := Real.sqrt_pos.2 hTreal
  have hratio : (B / Real.sqrt (T : ℝ)) ^ 2 =
      B ^ 2 / (T : ℝ) := by
    rw [div_pow, Real.sq_sqrt (le_of_lt hTreal)]
  have herrsq : err T ^ 2 ≤
      (B / Real.sqrt (T : ℝ)) ^ 2 := by
    rw [hratio]
    exact hdiv
  have herr : 0 ≤ err T := by
    dsimp [err]
    positivity
  have hratio_nonneg : 0 ≤ B / Real.sqrt (T : ℝ) :=
    div_nonneg hB (le_of_lt hsqrt)
  have herr_le : err T ≤ B / Real.sqrt (T : ℝ) := by
    nlinarith
  calc
    Metric.infDist (avg T) C ≤ dist (avg T) (proj T) :=
      Metric.infDist_le_dist_of_mem (hproj T)
    _ = err T := by simp [dist_eq_norm, err]
    _ ≤ B / Real.sqrt T := herr_le

/- The robust form of the certificate theorem.

The half-space inequality may have a uniform additive error `epsilon`.  The
result records the resulting non-vanishing error floor explicitly:

  dist(avg T, C) ≤ sqrt (B² / T + epsilon).

This is useful when the response is computed approximately or when a game
oracle only enforces the supporting half-space up to numerical tolerance.
-/
theorem blackwell_approximate_bound {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {C : Set E} (x avg proj : ℕ → E)
    (B epsilon : ℝ) (hproj : ∀ t : ℕ, proj t ∈ C)
    (hmin : ∀ t : ℕ, ∀ z ∈ C,
      ‖avg t - proj t‖ ≤ ‖avg t - z‖)
    (havg : ∀ t : ℕ, ((t : ℝ) + 1) • avg (t + 1) =
      (t : ℝ) • avg t + x t)
    (hinner : ∀ t : ℕ,
      inner ℝ (avg t - proj t) (x t - proj t) ≤ epsilon)
    (hbound : ∀ t : ℕ, ‖x t - proj t‖ ≤ B)
    (hB : 0 ≤ B) (hepsilon : 0 ≤ epsilon) :
    ∀ {T : ℕ}, 0 < T →
      Metric.infDist (avg T) C ≤ Real.sqrt (B ^ 2 / T + epsilon) := by
  intro T hT
  let err : ℕ → ℝ := fun t => ‖avg t - proj t‖
  have henergy : ∀ t : ℕ, (t : ℝ) ^ 2 * err t ^ 2 ≤
      (t : ℝ) * B ^ 2 + epsilon * (t : ℝ) * ((t : ℝ) - 1) := by
    intro t
    induction t with
    | zero => simp
    | succ t ih =>
        have hstep := blackwell_step_sq_error x avg proj B epsilon t hproj hmin
          (havg t) (hinner t) (hbound t)
        dsimp [err] at ih ⊢
        simpa [Nat.cast_succ] using (show
          ((t : ℝ) + 1) ^ 2 *
              ‖avg (t + 1) - proj (t + 1)‖ ^ 2 ≤
            ((t : ℝ) + 1) * B ^ 2 +
              epsilon * ((t : ℝ) + 1) * ((t : ℝ) + 1 - 1) by
          nlinarith [hstep, ih])
  have hTreal : 0 < (T : ℝ) := by exact_mod_cast hT
  have henergyT : (T : ℝ) ^ 2 * err T ^ 2 ≤
      (T : ℝ) * B ^ 2 + epsilon * (T : ℝ) * ((T : ℝ) - 1) :=
    henergy T
  have hdivide : (T : ℝ) * err T ^ 2 ≤
      B ^ 2 + epsilon * ((T : ℝ) - 1) := by
    apply le_of_mul_le_mul_left _ hTreal
    calc
      (T : ℝ) * ((T : ℝ) * err T ^ 2) =
          (T : ℝ) ^ 2 * err T ^ 2 := by ring
      _ ≤ (T : ℝ) * B ^ 2 + epsilon * (T : ℝ) * ((T : ℝ) - 1) := henergyT
      _ = (T : ℝ) * (B ^ 2 + epsilon * ((T : ℝ) - 1)) := by ring
  have hdiv : err T ^ 2 ≤
      B ^ 2 / (T : ℝ) + epsilon * (((T : ℝ) - 1) / (T : ℝ)) := by
    have hrepr : B ^ 2 / (T : ℝ) +
        epsilon * (((T : ℝ) - 1) / (T : ℝ)) =
        (B ^ 2 + epsilon * ((T : ℝ) - 1)) / (T : ℝ) := by
      field_simp
    rw [hrepr]
    exact (le_div_iff₀ hTreal).2 (by simpa [mul_comm] using hdivide)
  have hratio : B ^ 2 / (T : ℝ) +
      epsilon * (((T : ℝ) - 1) / (T : ℝ)) ≤ B ^ 2 / (T : ℝ) + epsilon := by
    have hfrac : ((T : ℝ) - 1) / (T : ℝ) ≤ 1 := by
      rw [div_le_iff₀ hTreal]
      linarith
    nlinarith
  have herrsq : err T ^ 2 ≤ B ^ 2 / (T : ℝ) + epsilon := hdiv.trans hratio
  have hq : 0 ≤ B ^ 2 / (T : ℝ) + epsilon := by positivity
  have hsqrt : 0 ≤ Real.sqrt (B ^ 2 / (T : ℝ) + epsilon) := Real.sqrt_nonneg _
  have herr : 0 ≤ err T := by
    dsimp [err]
    positivity
  have herr_le : err T ≤ Real.sqrt (B ^ 2 / (T : ℝ) + epsilon) := by
    have hsquare := Real.sq_sqrt hq
    nlinarith
  calc
    Metric.infDist (avg T) C ≤ dist (avg T) (proj T) :=
      Metric.infDist_le_dist_of_mem (hproj T)
    _ = err T := by simp [dist_eq_norm, err]
    _ ≤ Real.sqrt (B ^ 2 / T + epsilon) := herr_le

/- An online response oracle generates the running average recursively. This
   packages the certificate theorem for an actual sequential payoff rule while
   leaving the strategic response condition explicit. -/

noncomputable def responseAverage {E : Type*} [AddCommGroup E] [Module ℝ E]
    (response : E → E) : ℕ → E
  | 0 => 0
  | t + 1 => ((t : ℝ) + 1)⁻¹ •
      ((t : ℝ) • responseAverage response t +
        response (responseAverage response t))

/- An adaptive running average whose stage payoff may depend on time as well
   as on the current average.  This is the form needed for a repeated game:
   the opponent's action at time `t` is not known when earlier averages are
   formed. -/
noncomputable def adaptiveAverage {E : Type*} [AddCommGroup E] [Module ℝ E]
    (stage : ℕ → E → E) : ℕ → E
  | 0 => 0
  | t + 1 => ((t : ℝ) + 1)⁻¹ •
      ((t : ℝ) • adaptiveAverage stage t + stage t (adaptiveAverage stage t))

lemma responseAverage_step {E : Type*} [AddCommGroup E] [Module ℝ E]
    (response : E → E) (t : ℕ) :
    ((t : ℝ) + 1) • responseAverage response (t + 1) =
      (t : ℝ) • responseAverage response t +
        response (responseAverage response t) := by
  rw [responseAverage]
  rw [smul_smul]
  field_simp
  simp

lemma adaptiveAverage_step {E : Type*} [AddCommGroup E] [Module ℝ E]
    (stage : ℕ → E → E) (t : ℕ) :
    ((t : ℝ) + 1) • adaptiveAverage stage (t + 1) =
      (t : ℝ) • adaptiveAverage stage t + stage t (adaptiveAverage stage t) := by
  rw [adaptiveAverage]
  rw [smul_smul]
  field_simp
  simp

theorem blackwell_response_bound {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {C : Set E} (response projection : E → E) (B : ℝ)
    (hproj : ∀ y : E, projection y ∈ C)
    (hmin : ∀ y : E, ∀ z ∈ C,
      ‖y - projection y‖ ≤ ‖y - z‖)
    (hinner : ∀ y : E,
      inner ℝ (y - projection y) (response y - projection y) ≤ 0)
    (hbound : ∀ y : E, ‖response y - projection y‖ ≤ B) (hB : 0 ≤ B) :
    ∀ {T : ℕ}, 0 < T →
      Metric.infDist (responseAverage response T) C ≤ B / Real.sqrt T := by
  let avg : ℕ → E := responseAverage response
  let x : ℕ → E := fun t => response (avg t)
  let proj : ℕ → E := fun t => projection (avg t)
  have havg : ∀ t : ℕ, ((t : ℝ) + 1) • avg (t + 1) =
      (t : ℝ) • avg t + x t := by
    intro t
    exact responseAverage_step response t
  have hproj' : ∀ t : ℕ, proj t ∈ C := by
    intro t
    exact hproj (avg t)
  have hmin' : ∀ t : ℕ, ∀ z ∈ C,
      ‖avg t - proj t‖ ≤ ‖avg t - z‖ := by
    intro t z hz
    exact hmin (avg t) z hz
  have hinner' : ∀ t : ℕ,
      inner ℝ (avg t - proj t) (x t - proj t) ≤ 0 := by
    intro t
    exact hinner (avg t)
  have hbound' : ∀ t : ℕ, ‖x t - proj t‖ ≤ B := by
    intro t
    exact hbound (avg t)
  intro T hT
  simpa [avg] using (blackwell_approachability_bound x avg proj B hproj'
    hmin' havg hinner' hbound' hB (T := T) hT)

/-- A running average satisfies the affine recurrence used above. -/
noncomputable def runningAverage {E : Type*} [AddCommGroup E] [Module ℝ E]
    (x : ℕ → E) (T : ℕ) : E :=
  (T : ℝ)⁻¹ • ∑ t ∈ Finset.range T, x t

lemma runningAverage_zero {E : Type*} [AddCommGroup E] [Module ℝ E]
    (x : ℕ → E) : runningAverage x 0 = 0 := by
  simp [runningAverage]

lemma runningAverage_step {E : Type*} [AddCommGroup E] [Module ℝ E]
    (x : ℕ → E) (t : ℕ) :
    ((t : ℝ) + 1) • runningAverage x (t + 1) =
      (t : ℝ) • runningAverage x t + x t := by
  by_cases ht : t = 0
  · subst t
    simp [runningAverage]
  · have ht' : (t : ℝ) ≠ 0 := by exact_mod_cast ht
    simp only [runningAverage, Finset.sum_range_succ, Nat.cast_add,
      Nat.cast_one]
    rw [smul_smul, smul_smul]
    field_simp [ht', show (t : ℝ) + 1 ≠ 0 by positivity]
    module

/-- A closest point and its normal-cone inequality exist for every nonempty
    closed convex target. -/
theorem exists_projection {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] {C : Set E}
    (hne : C.Nonempty) (hclosed : IsClosed C) (hconvex : Convex ℝ C)
    (y : E) :
    ∃ p ∈ C, ‖y - p‖ = Metric.infDist y C ∧
      ∀ z ∈ C, inner ℝ (y - p) (z - p) ≤ 0 := by
  obtain ⟨p, hp, hnorm⟩ := exists_norm_eq_iInf_of_complete_convex
    hne hclosed.isComplete hconvex y
  have hinf : Metric.infDist y C = ⨅ z : C, ‖y - (z : E)‖ := by
    rw [Metric.infDist_eq_iInf]
    apply iInf_congr
    intro z
    rw [dist_eq_norm]
  have hnormal :=
    (norm_eq_iInf_iff_real_inner_le_zero hconvex hp).mp hnorm
  refine ⟨p, hp, ?_, hnormal⟩
  rw [hinf]
  exact hnorm

end Approachability
end Blackwell
