import Mathlib.Tactic

set_option autoImplicit false

/-
# A quantitative approachability-to-regret reduction

For a finite action set, a vector of average regrets is approachable toward
the coordinatewise nonpositive orthant exactly when every fixed-action regret
is controlled.  This file isolates the quantitative part of that reduction:
an ℓ2 distance certificate gives a coordinatewise regret certificate with no
additional dimension factor, while the reverse estimate is dimension
dependent.
-/

namespace Blackwell
namespace Reduction

open scoped BigOperators

noncomputable def l2Norm {A : Type*} [Fintype A] (v : A → ℝ) : ℝ :=
  Real.sqrt (∑ a, v a ^ 2)

lemma l2Norm_nonneg {A : Type*} [Fintype A] (v : A → ℝ) :
    0 ≤ l2Norm v := by
  exact Real.sqrt_nonneg _

lemma coordinate_le_l2 {A : Type*} [Fintype A] (v : A → ℝ) (a : A) :
    v a ≤ l2Norm v := by
  have hsum : v a ^ 2 ≤ ∑ b, v b ^ 2 := by
    exact Finset.single_le_sum (fun b _ => sq_nonneg (v b)) (Finset.mem_univ a)
  have hroot : Real.sqrt (v a ^ 2) ≤ Real.sqrt (∑ b, v b ^ 2) :=
    Real.sqrt_le_sqrt hsum
  rw [Real.sqrt_sq_eq_abs] at hroot
  exact (le_abs_self (v a)).trans (by simpa [l2Norm] using hroot)

lemma l2Norm_le_sqrt_card_mul {A : Type*} [Fintype A]
    (v : A → ℝ) (rho : ℝ) (hrho : 0 ≤ rho)
    (hcoord : ∀ a : A, |v a| ≤ rho) :
    l2Norm v ≤ Real.sqrt (Fintype.card A) * rho := by
  have hsum : (∑ a, v a ^ 2) ≤
      (Fintype.card A : ℝ) * rho ^ 2 := by
    calc
      (∑ a, v a ^ 2) ≤ ∑ a, rho ^ 2 := by
        exact Finset.sum_le_sum fun a _ => by
          have ha : 0 ≤ |v a| := abs_nonneg _
          have hsq : |v a| ^ 2 ≤ rho ^ 2 := by
            nlinarith [hcoord a]
          simpa [sq_abs] using hsq
      _ = (Fintype.card A : ℝ) * rho ^ 2 := by simp
  have hroot : Real.sqrt (∑ a, v a ^ 2) ≤
      Real.sqrt ((Fintype.card A : ℝ) * rho ^ 2) :=
    Real.sqrt_le_sqrt hsum
  rw [Real.sqrt_mul (Nat.cast_nonneg (Fintype.card A)),
    Real.sqrt_sq_eq_abs, abs_of_nonneg hrho] at hroot
  simpa [l2Norm] using hroot

lemma l2Norm_const {A : Type*} [Fintype A] (rho : ℝ) (hrho : 0 ≤ rho) :
    l2Norm (fun _ : A => rho) = Real.sqrt (Fintype.card A) * rho := by
  rw [l2Norm]
  have hsum : (∑ _ : A, rho ^ 2) = (Fintype.card A : ℝ) * rho ^ 2 := by
    simp
  rw [hsum, Real.sqrt_mul (Nat.cast_nonneg (Fintype.card A)),
    Real.sqrt_sq_eq_abs, abs_of_nonneg hrho]

theorem dimension_factor_is_attained {A : Type*} [Fintype A] (rho : ℝ)
    (hrho : 0 ≤ rho) :
    l2Norm (fun _ : A => rho) = Real.sqrt (Fintype.card A) * rho := by
  exact l2Norm_const rho hrho

def regretVector {A : Type*} (loss : ℕ → A → ℝ) (actions : ℕ → A)
    (t : ℕ) : A → ℝ :=
  fun a => loss t (actions t) - loss t a

noncomputable def averageRegret {A : Type*} [Fintype A]
    (loss : ℕ → A → ℝ) (actions : ℕ → A) (T : ℕ) : A → ℝ :=
  fun a => (T : ℝ)⁻¹ *
    ∑ t ∈ Finset.range T, (loss t (actions t) - loss t a)

theorem regret_coordinate_of_l2_bound {A : Type*} [Fintype A]
    (loss : ℕ → A → ℝ) (actions : ℕ → A) (T : ℕ) (delta : ℝ)
    (hdelta : l2Norm (averageRegret loss actions T) ≤ delta) :
    ∀ a : A, averageRegret loss actions T a ≤ delta := by
  intro a
  exact (coordinate_le_l2 (averageRegret loss actions T) a).trans hdelta

theorem approachability_witness_implies_regret {A : Type*} [Fintype A]
    (v z : A → ℝ) (delta : ℝ)
    (hz : ∀ a : A, z a ≤ 0)
    (hdist : l2Norm (fun a => v a - z a) ≤ delta) :
    ∀ a : A, v a ≤ delta := by
  intro a
  have hz' : v a ≤ v a - z a := by linarith [hz a]
  exact hz'.trans ((coordinate_le_l2 (fun b => v b - z b) a).trans hdist)

theorem average_regret_witness_implies_coordinate_bound
    {A : Type*} [Fintype A]
    (loss : ℕ → A → ℝ) (actions : ℕ → A) (T : ℕ) (z : A → ℝ) (delta : ℝ)
    (hz : ∀ a : A, z a ≤ 0)
    (hdist : l2Norm (fun a => averageRegret loss actions T a - z a) ≤
      delta) :
    ∀ a : A, averageRegret loss actions T a ≤ delta := by
  exact approachability_witness_implies_regret
    (averageRegret loss actions T) z _ hz hdist

end Reduction
end Blackwell
