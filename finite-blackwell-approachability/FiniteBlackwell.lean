import Mathlib.Topology.Sion
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Tactic

set_option autoImplicit false

/-!
# A finite Blackwell strategy from minimax

This project aims to close the strategic gap between Blackwell's scalar
half-space condition and a causal finite-game strategy with an explicit
approachability rate.  It is independent of the repository's other formal
entries and imports Mathlib only.
-/

namespace Blackwell.FiniteApproachability

open Set
open scoped BigOperators RealInnerProductSpace

noncomputable section

/-- A finite real probability vector. -/
def simplex {α : Type*} [Fintype α] (p : α → ℝ) : Prop :=
  (∀ a, 0 ≤ p a) ∧ (∑ a, p a) = 1

/-- The set of finite mixed actions, viewed as a convex subset of a function space. -/
def simplexSet (α : Type*) [Fintype α] : Set (α → ℝ) :=
  {p | simplex p}

/-- A bundled finite mixed action. -/
abbrev Mixed (α : Type*) [Fintype α] := {p : α → ℝ // simplex p}

lemma simplexSet_nonempty {α : Type*} [Fintype α] [Nonempty α] :
    (simplexSet α).Nonempty := by
  classical
  let p : α → ℝ := fun _ => (Fintype.card α : ℝ)⁻¹
  refine ⟨p, ?_⟩
  change (∀ a, 0 ≤ p a) ∧ (∑ a, p a) = 1
  constructor
  · intro a
    positivity
  · have hcard : (Fintype.card α : ℝ) ≠ 0 := by
      exact_mod_cast (Fintype.card_ne_zero : Fintype.card α ≠ 0)
    simp [p, hcard]

lemma simplexSet_convex {α : Type*} [Fintype α] :
    Convex ℝ (simplexSet α) := by
  intro p hp q hq a b ha hb hab
  change simplex p at hp
  change simplex q at hq
  change simplex (a • p + b • q)
  constructor
  · intro i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact add_nonneg (mul_nonneg ha (hp.1 i)) (mul_nonneg hb (hq.1 i))
  · simp [Finset.sum_add_distrib, ← Finset.mul_sum, hp.2, hq.2, hab]

lemma simplexSet_isClosed {α : Type*} [Fintype α] :
    IsClosed (simplexSet α) := by
  have hnonneg : IsClosed {p : α → ℝ | ∀ a, 0 ≤ p a} := by
    rw [Set.ofPred_forall]
    exact isClosed_iInter fun a => isClosed_Ici.preimage (continuous_apply a)
  have hsum : Continuous (fun p : α → ℝ => ∑ a, p a) := by
    fun_prop
  have hmass : IsClosed {p : α → ℝ | ∑ a, p a = 1} :=
    isClosed_singleton.preimage hsum
  change IsClosed ({p : α → ℝ | ∀ a, 0 ≤ p a} ∩
    {p : α → ℝ | ∑ a, p a = 1})
  exact hnonneg.inter hmass

lemma simplexSet_isBounded {α : Type*} [Fintype α] :
    Bornology.IsBounded (simplexSet α) := by
  rw [Metric.isBounded_iff_subset_closedBall (0 : α → ℝ)]
  refine ⟨1, ?_⟩
  intro p hp
  change simplex p at hp
  rw [Metric.mem_closedBall, dist_zero_right,
    pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)]
  intro i
  rw [Real.norm_eq_abs, abs_of_nonneg (hp.1 i)]
  calc
    p i ≤ ∑ j, p j :=
      Finset.single_le_sum (fun j _ => hp.1 j) (Finset.mem_univ i)
    _ = 1 := hp.2

lemma simplexSet_isCompact {α : Type*} [Fintype α] :
    IsCompact (simplexSet α) := by
  rw [Metric.isCompact_iff_isClosed_bounded]
  exact ⟨simplexSet_isClosed (α := α), simplexSet_isBounded (α := α)⟩

/-- The pure mixed action concentrated at one finite action. -/
noncomputable def pointMass {α : Type*} (a : α) : α → ℝ := by
  classical
  exact fun b => if b = a then 1 else 0

lemma pointMass_mem_simplexSet {α : Type*} [Fintype α] (a : α) :
    pointMass a ∈ simplexSet α := by
  classical
  constructor
  · intro b
    by_cases h : b = a <;> simp [pointMass, h]
  · simp [pointMass]

/-- A closest point in a nonempty closed convex set, with its normal inequality. -/
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

/-- A chosen nearest point in a nonempty closed convex target. -/
noncomputable def closestPoint {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] {C : Set E}
    (hne : C.Nonempty) (hclosed : IsClosed C) (hconvex : Convex ℝ C) : E → E :=
  fun y => Classical.choose (exists_projection hne hclosed hconvex y)

lemma closestPoint_spec {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] {C : Set E}
    (hne : C.Nonempty) (hclosed : IsClosed C) (hconvex : Convex ℝ C) (y : E) :
    closestPoint hne hclosed hconvex y ∈ C ∧
      ‖y - closestPoint hne hclosed hconvex y‖ = Metric.infDist y C ∧
      ∀ z ∈ C, inner ℝ (y - closestPoint hne hclosed hconvex y)
        (z - closestPoint hne hclosed hconvex y) ≤ 0 := by
  simpa [closestPoint] using
    Classical.choose_spec (exists_projection hne hclosed hconvex y)

/-- The expected vector payoff of a mixed action against one pure response. -/
def expectedPayoff {A B E : Type*} [Fintype A]
    [AddCommMonoid E] [Module ℝ E]
    (p : A → ℝ) (g : A → B → E) (b : B) : E :=
  ∑ a, p a • g a b

/-- Expected payoff when both players use mixed actions. -/
def mixedExpectedPayoff {A B E : Type*} [Fintype A] [Fintype B]
    [AddCommMonoid E] [Module ℝ E]
    (p : A → ℝ) (q : B → ℝ) (g : A → B → E) : E :=
  ∑ b, q b • expectedPayoff p g b

/-- The scalar half-space payoff used in the minimax condition. -/
def normalScore {A B E : Type*} [Fintype A] [Fintype B]
    [AddCommGroup E] [Module ℝ E] [Inner ℝ E]
    (g : A → B → E) (y z : E) (p : A → ℝ) (q : B → ℝ) : ℝ :=
  inner ℝ (y - z) (mixedExpectedPayoff p q g)

lemma mixedExpectedPayoff_pointMass {A B E : Type*} [Fintype A] [Fintype B]
    [AddCommMonoid E] [Module ℝ E]
    (p : A → ℝ) (g : A → B → E) (b : B) :
    mixedExpectedPayoff p (pointMass b) g = expectedPayoff p g b := by
  classical
  simp [mixedExpectedPayoff, pointMass]

lemma expectedPayoff_norm_le {A B E : Type*} [Fintype A]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (p : A → ℝ) (hp : simplex p) (g : A → B → E) (b : B)
    (G : ℝ) (hpay : ∀ a, ‖g a b‖ ≤ G) :
    ‖expectedPayoff p g b‖ ≤ G := by
  rw [expectedPayoff]
  calc
    ‖∑ a, p a • g a b‖ ≤ ∑ a, ‖p a • g a b‖ := norm_sum_le _ _
    _ ≤ ∑ a, p a * G := by
      apply Finset.sum_le_sum
      intro a _
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hp.1 a)]
      exact mul_le_mul_of_nonneg_left (hpay a) (hp.1 a)
    _ = G := by
      rw [← Finset.sum_mul, hp.2]
      ring

lemma expectedPayoffAgainst_norm_le {A B E : Type*} [Fintype A]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (p : A → ℝ) (hp : simplex p) (g : A → B → E) (b : B)
    (G : ℝ) (hpay : ∀ a, ‖g a b‖ ≤ G) :
    ‖expectedPayoff p g b‖ ≤ G :=
  expectedPayoff_norm_le p hp g b G hpay

/-- A pointwise scalar Blackwell condition against every mixed opponent action. -/
def mixedBlackwellCondition {A B E : Type*} [Fintype A] [Fintype B]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (g : A → B → E) {C : Set E}
    (hne : C.Nonempty) (hclosed : IsClosed C) (hconvex : Convex ℝ C) : Prop :=
  ∀ y : E, ∀ q : B → ℝ, q ∈ simplexSet B →
    ∃ p : A → ℝ, p ∈ simplexSet A ∧
      normalScore g y (closestPoint hne hclosed hconvex y) p q ≤
        inner ℝ (y - closestPoint hne hclosed hconvex y)
          (closestPoint hne hclosed hconvex y)

private def payoffLeftMap {A B E : Type*} [Fintype A] [Fintype B]
    [AddCommMonoid E] [Module ℝ E]
    (g : A → B → E) (q : B → ℝ) : (A → ℝ) →ₗ[ℝ] E where
  toFun := fun p => mixedExpectedPayoff p q g
  map_add' := by
    intro p p'
    simp [mixedExpectedPayoff, expectedPayoff, Finset.sum_add_distrib, add_smul]
  map_smul' := by
    intro c p
    simp [mixedExpectedPayoff, expectedPayoff, Pi.smul_apply, Finset.smul_sum,
      smul_smul, mul_left_comm]

private def payoffRightMap {A B E : Type*} [Fintype A] [Fintype B]
    [AddCommMonoid E] [Module ℝ E]
    (g : A → B → E) (p : A → ℝ) : (B → ℝ) →ₗ[ℝ] E where
  toFun := fun q => mixedExpectedPayoff p q g
  map_add' := by
    intro q q'
    simp [mixedExpectedPayoff, Finset.sum_add_distrib, add_smul]
  map_smul' := by
    intro c q
    simp [mixedExpectedPayoff, Pi.smul_apply, Finset.smul_sum,
      smul_smul]

private def normalScoreLeftMap {A B E : Type*} [Fintype A] [Fintype B]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (g : A → B → E) (y z : E) (q : B → ℝ) :
    (A → ℝ) →ₗ[ℝ] ℝ :=
  (innerSL ℝ (y - z)).toLinearMap.comp (payoffLeftMap g q)

private def normalScoreRightMap {A B E : Type*} [Fintype A] [Fintype B]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (g : A → B → E) (y z : E) (p : A → ℝ) :
    (B → ℝ) →ₗ[ℝ] ℝ :=
  (innerSL ℝ (y - z)).toLinearMap.comp (payoffRightMap g p)

private lemma normalScoreLeftMap_apply {A B E : Type*} [Fintype A] [Fintype B]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (g : A → B → E) (y z : E) (q : B → ℝ) (p : A → ℝ) :
    normalScoreLeftMap g y z q p = normalScore g y z p q := by
  rfl

private lemma normalScoreRightMap_apply {A B E : Type*} [Fintype A] [Fintype B]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (g : A → B → E) (y z : E) (p : A → ℝ) (q : B → ℝ) :
    normalScoreRightMap g y z p q = normalScore g y z p q := by
  rfl

/-- Sion minimax turns mixed-opponent feasibility into one uniform response. -/
theorem exists_uniform_mixed_response {A B E : Type*}
    [Fintype A] [Fintype B] [Nonempty A] [Nonempty B]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (g : A → B → E) (y z : E)
    (hfeasible : ∀ q : B → ℝ, q ∈ simplexSet B →
      ∃ p : A → ℝ, p ∈ simplexSet A ∧
        normalScore g y z p q ≤ inner ℝ (y - z) z) :
    ∃ p : A → ℝ, p ∈ simplexSet A ∧
      ∀ q : B → ℝ, q ∈ simplexSet B →
        normalScore g y z p q ≤ inner ℝ (y - z) z := by
  let f : (A → ℝ) → (B → ℝ) → ℝ := normalScore g y z
  have hfy : ∀ q ∈ simplexSet B,
      LowerSemicontinuousOn (fun p : A → ℝ => f p q) (simplexSet A) := by
    intro q hq
    have hcont : Continuous (fun p : A → ℝ => f p q) := by
      simpa [f, ← normalScoreLeftMap_apply] using
        (normalScoreLeftMap g y z q).continuous_of_finiteDimensional
    exact hcont.continuousOn.lowerSemicontinuousOn
  have hfy' : ∀ q ∈ simplexSet B,
      QuasiconvexOn ℝ (simplexSet A) (fun p : A → ℝ => f p q) := by
    intro q hq
    simpa [f, ← normalScoreLeftMap_apply] using
      ((normalScoreLeftMap g y z q).convexOn
        (simplexSet_convex (α := A))).quasiconvexOn
  have hfx : ∀ p ∈ simplexSet A,
      UpperSemicontinuousOn (fun q : B → ℝ => f p q) (simplexSet B) := by
    intro p hp
    have hcont : Continuous (fun q : B → ℝ => f p q) := by
      simpa [f, ← normalScoreRightMap_apply] using
        (normalScoreRightMap g y z p).continuous_of_finiteDimensional
    exact hcont.continuousOn.upperSemicontinuousOn
  have hfx' : ∀ p ∈ simplexSet A,
      QuasiconcaveOn ℝ (simplexSet B) (fun q : B → ℝ => f p q) := by
    intro p hp
    simpa [f, ← normalScoreRightMap_apply] using
      (neg_convexOn_iff.mp
        ((-normalScoreRightMap g y z p).convexOn
          (simplexSet_convex (α := B)))).quasiconcaveOn
  obtain ⟨p, hp, q, hq, hsaddle⟩ := Sion.exists_isSaddlePointOn
      (f := f) (ne_X := simplexSet_nonempty (α := A))
      (cX := simplexSet_convex (α := A))
      (kX := simplexSet_isCompact (α := A)) hfy hfy'
      (cY := simplexSet_convex (α := B))
      (ne_Y := simplexSet_nonempty (α := B))
      (kY := simplexSet_isCompact (α := B)) hfx hfx'
  obtain ⟨p₀, hp₀, h₀⟩ := hfeasible q hq
  have hpq : f p q ≤ f p₀ q := hsaddle p₀ hp₀ q hq
  have hlevel : f p q ≤ inner ℝ (y - z) z := hpq.trans h₀
  refine ⟨p, hp, ?_⟩
  intro q' hq'
  exact (hsaddle p hp q' hq').trans hlevel

end

end Blackwell.FiniteApproachability
