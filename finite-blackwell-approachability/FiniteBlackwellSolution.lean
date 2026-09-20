import Mathlib
import FiniteBlackwellRate

set_option autoImplicit false

namespace Blackwell.FiniteApproachability.Palomar

open Set
open scoped BigOperators RealInnerProductSpace

noncomputable section

universe u

abbrev FiniteEuclideanSpace (I : Type u) : Type u := I → ℝ

private abbrev euclideanEquiv {I : Type*} [Fintype I] :
    EuclideanSpace ℝ I ≃L[ℝ] (I → ℝ) :=
  PiLp.continuousLinearEquiv 2 ℝ (fun _ : I => ℝ)

private def coreTarget {I : Type*} [Fintype I]
    (C : Set (I → ℝ)) : Set (EuclideanSpace ℝ I) :=
  euclideanEquiv ⁻¹' C

private noncomputable def coreTargetEquiv {I : Type*} [Fintype I]
    (C : Set (I → ℝ)) :
    {x : EuclideanSpace ℝ I // x ∈ coreTarget C} ≃ C where
  toFun x := ⟨euclideanEquiv x.1, x.2⟩
  invFun x := ⟨euclideanEquiv.symm x.1, by
    change euclideanEquiv (euclideanEquiv.symm x.1) ∈ C
    rw [euclideanEquiv.apply_symm_apply]
    exact x.2⟩
  left_inv x := by
    apply Subtype.ext
    exact euclideanEquiv.symm_apply_apply x.1
  right_inv x := by
    apply Subtype.ext
    exact euclideanEquiv.apply_symm_apply x.1

/-- The standard coordinate dot product on a finite real Euclidean space. -/
def coordinateInner {I : Type*} [Fintype I]
    (x y : (I → ℝ)) : ℝ :=
  ∑ i, x i * y i

/-- The Euclidean norm written directly in finite coordinates. -/
def coordinateNorm {I : Type*} [Fintype I]
    (x : (I → ℝ)) : ℝ :=
  Real.sqrt (∑ i, x i ^ 2)

/-- The Euclidean distance written directly in finite coordinates. -/
def coordinateDistance {I : Type*} [Fintype I]
    (x y : (I → ℝ)) : ℝ :=
  coordinateNorm (x - y)

/-- Distance to a set, as the infimum of the finite-coordinate distances. -/
noncomputable def coordinateInfDist {I : Type*} [Fintype I]
    (x : (I → ℝ)) (C : Set (I → ℝ)) : ℝ :=
  ⨅ z : C, coordinateDistance x z.1

private theorem coordinateInner_eq_coreInner {I : Type*} [Fintype I]
    (x y : (I → ℝ)) :
    coordinateInner x y = inner ℝ (euclideanEquiv.symm x) (euclideanEquiv.symm y) := by
  simp only [coordinateInner, euclideanEquiv,
    PiLp.coe_symm_continuousLinearEquiv, PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Real.inner_apply]

private theorem coordinateInner_sub_right {I : Type*} [Fintype I]
    (x y z : I → ℝ) :
    coordinateInner x (y - z) = coordinateInner x y - coordinateInner x z := by
  rw [coordinateInner_eq_coreInner, coordinateInner_eq_coreInner,
    coordinateInner_eq_coreInner, map_sub, inner_sub_right]

private theorem coordinateNorm_eq_coreNorm {I : Type*} [Fintype I]
    (x : (I → ℝ)) :
    coordinateNorm x = ‖euclideanEquiv.symm x‖ := by
  simp [coordinateNorm, euclideanEquiv, PiLp.norm_eq_of_L2,
    Real.norm_eq_abs, sq_abs]

private theorem coordinateNorm_sub_le {I : Type*} [Fintype I]
    (x y : I → ℝ) :
    coordinateNorm (x - y) ≤ coordinateNorm x + coordinateNorm y := by
  calc
    coordinateNorm (x - y) = ‖euclideanEquiv.symm x - euclideanEquiv.symm y‖ := by
      rw [coordinateNorm_eq_coreNorm, map_sub]
    _ ≤ ‖euclideanEquiv.symm x‖ + ‖euclideanEquiv.symm y‖ := norm_sub_le _ _
    _ = coordinateNorm x + coordinateNorm y := by
      rw [← coordinateNorm_eq_coreNorm, ← coordinateNorm_eq_coreNorm]

private theorem coordinateDistance_eq_coreDist {I : Type*} [Fintype I]
    (x y : (I → ℝ)) :
    coordinateDistance x y = dist (euclideanEquiv.symm x) (euclideanEquiv.symm y) := by
  rw [coordinateDistance, coordinateNorm_eq_coreNorm, dist_eq_norm]
  exact congrArg norm (euclideanEquiv.symm.map_sub x y).symm

private theorem coordinateInfDist_eq_coreInfDist {I : Type*} [Fintype I]
    (x : (I → ℝ)) (C : Set (I → ℝ)) :
    coordinateInfDist x C = Metric.infDist (euclideanEquiv.symm x) (coreTarget C) := by
  let eC := coreTargetEquiv C
  calc
    coordinateInfDist x C =
        ⨅ z : coreTarget C, coordinateDistance x (eC z).1 :=
      (eC.iInf_congr (fun _ => rfl)).symm
    _ = ⨅ z : coreTarget C, dist (euclideanEquiv.symm x) z.1 := by
      apply iInf_congr
      intro z
      simpa [eC, coreTargetEquiv] using
        (coordinateDistance_eq_coreDist x (eC z).1)
    _ = Metric.infDist (euclideanEquiv.symm x) (coreTarget C) := by
      rw [Metric.infDist_eq_iInf]

private theorem coreTarget_nonempty {I : Type*} [Fintype I]
    {C : Set (I → ℝ)} (hne : C.Nonempty) :
    (coreTarget C).Nonempty := by
  rcases hne with ⟨x, hx⟩
  refine ⟨euclideanEquiv.symm x, ?_⟩
  change euclideanEquiv (euclideanEquiv.symm x) ∈ C
  rw [euclideanEquiv.apply_symm_apply]
  exact hx

private theorem coreTarget_isClosed {I : Type*} [Fintype I]
    {C : Set (I → ℝ)} (hclosed : IsClosed C) :
    IsClosed (coreTarget C) :=
  hclosed.preimage euclideanEquiv.continuous

private theorem coreTarget_convex {I : Type*} [Fintype I]
    {C : Set (I → ℝ)} (hconvex : Convex ℝ C) :
    Convex ℝ (coreTarget C) :=
  hconvex.linear_preimage euclideanEquiv.toLinearMap

/-- A closest-point witness and its normal-cone inequality. -/
theorem exists_projection {I : Type*} [Fintype I]
    {C : Set (I → ℝ)}
    (hne : C.Nonempty) (hclosed : IsClosed C) (hconvex : Convex ℝ C)
    (y : (I → ℝ)) :
    ∃ p ∈ C, coordinateDistance y p = coordinateInfDist y C ∧
      ∀ z ∈ C, coordinateInner (y - p) (z - p) ≤ 0 := by
  let C' := coreTarget C
  have hne' : C'.Nonempty := coreTarget_nonempty hne
  have hclosed' : IsClosed C' := coreTarget_isClosed hclosed
  have hconvex' : Convex ℝ C' := coreTarget_convex hconvex
  obtain ⟨p', hp', hdist, hnormal⟩ :=
    Blackwell.FiniteApproachability.exists_projection
      hne' hclosed' hconvex' (euclideanEquiv.symm y)
  let p := euclideanEquiv p'
  have hinf := coordinateInfDist_eq_coreInfDist y C
  refine ⟨p, ?_, ?_, ?_⟩
  · change euclideanEquiv p' ∈ C
    exact hp'
  · calc
      coordinateDistance y p = dist (euclideanEquiv.symm y) (euclideanEquiv.symm p) :=
        coordinateDistance_eq_coreDist y p
      _ = dist (euclideanEquiv.symm y) p' := by simp [p]
      _ = ‖euclideanEquiv.symm y - p'‖ := dist_eq_norm _ _
      _ = Metric.infDist (euclideanEquiv.symm y) C' := hdist
      _ = coordinateInfDist y C := hinf.symm
  · intro z hz
    have hz' : euclideanEquiv.symm z ∈ C' := by
      change euclideanEquiv (euclideanEquiv.symm z) ∈ C
      rw [euclideanEquiv.apply_symm_apply]
      exact hz
    have h := hnormal (euclideanEquiv.symm z) hz'
    have hp : euclideanEquiv.symm p = p' := by
      simp [p]
    have hcoord : coordinateInner (y - p) (z - p) =
        inner ℝ (euclideanEquiv.symm y - p')
          (euclideanEquiv.symm z - p') := by
      calc
        coordinateInner (y - p) (z - p) =
            inner ℝ (euclideanEquiv.symm (y - p))
              (euclideanEquiv.symm (z - p)) := coordinateInner_eq_coreInner _ _
        _ = inner ℝ (euclideanEquiv.symm y - p')
              (euclideanEquiv.symm z - p') := by rw [map_sub, map_sub, hp]
    rw [hcoord]
    exact h

/-- A chosen nearest point in a nonempty closed convex target. -/
noncomputable abbrev closestPoint {I : Type*} [Fintype I]
    {C : Set (I → ℝ)}
    (hne : C.Nonempty) (hclosed : IsClosed C) (hconvex : Convex ℝ C) :
    (I → ℝ) → (I → ℝ) :=
  fun y => Classical.choose (exists_projection hne hclosed hconvex y)

lemma closestPoint_spec {I : Type*} [Fintype I]
    {C : Set (I → ℝ)}
    (hne : C.Nonempty) (hclosed : IsClosed C) (hconvex : Convex ℝ C)
    (y : (I → ℝ)) :
    closestPoint hne hclosed hconvex y ∈ C ∧
      coordinateDistance y (closestPoint hne hclosed hconvex y) = coordinateInfDist y C ∧
      ∀ z ∈ C, coordinateInner (y - closestPoint hne hclosed hconvex y)
        (z - closestPoint hne hclosed hconvex y) ≤ 0 := by
  simpa [closestPoint] using
    Classical.choose_spec (exists_projection hne hclosed hconvex y)

/-- The chosen nearest point lies in the target. -/
lemma closestPoint_mem {I : Type*} [Fintype I]
    {C : Set (I → ℝ)}
    (hne : C.Nonempty) (hclosed : IsClosed C) (hconvex : Convex ℝ C)
    (y : (I → ℝ)) : closestPoint hne hclosed hconvex y ∈ C :=
  (closestPoint_spec hne hclosed hconvex y).1

/-- Probability vectors on a finite action type. -/
def simplex {α : Type*} [Fintype α] (p : α → ℝ) : Prop :=
  (∀ a, 0 ≤ p a) ∧ (∑ a, p a) = 1

/-- The finite mixed-action simplex as a subset of its coordinate space. -/
def simplexSet (α : Type*) [Fintype α] : Set (α → ℝ) :=
  {p | simplex p}

/-- A bundled finite mixed action. -/
abbrev Mixed (α : Type*) [Fintype α] := {p : α → ℝ // simplex p}

/-- Expected payoff against one pure opponent action. -/
def expectedPayoff {A B I : Type*} [Fintype A] [Fintype I]
    (p : A → ℝ) (g : A → B → (I → ℝ)) (b : B) :
    (I → ℝ) :=
  ∑ a, p a • g a b

/-- Expected payoff when both players use mixed actions. -/
def mixedExpectedPayoff {A B I : Type*} [Fintype A] [Fintype B] [Fintype I]
    (p : A → ℝ) (q : B → ℝ) (g : A → B → (I → ℝ)) :
    (I → ℝ) :=
  ∑ b, q b • expectedPayoff p g b

private theorem mixedExpectedPayoff_pointMass {A B I : Type*}
    [Fintype A] [Fintype B] [Fintype I]
    (p : A → ℝ) (g : A → B → (I → ℝ)) (b : B) :
    mixedExpectedPayoff p (Blackwell.FiniteApproachability.pointMass b) g =
      expectedPayoff p g b := by
  simpa [mixedExpectedPayoff, expectedPayoff,
    Blackwell.FiniteApproachability.mixedExpectedPayoff,
    Blackwell.FiniteApproachability.expectedPayoff] using
    (Blackwell.FiniteApproachability.mixedExpectedPayoff_pointMass p g b)

private theorem map_expectedPayoff {A B I : Type*} [Fintype A] [Fintype I]
    (p : A → ℝ) (g : A → B → (I → ℝ)) (b : B) :
    euclideanEquiv.symm (expectedPayoff p g b) =
      Blackwell.FiniteApproachability.expectedPayoff p
        (fun a b => euclideanEquiv.symm (g a b)) b := by
  simp [expectedPayoff, Blackwell.FiniteApproachability.expectedPayoff,
    map_sum, map_smul]

private theorem map_mixedExpectedPayoff {A B I : Type*}
    [Fintype A] [Fintype B] [Fintype I]
    (p : A → ℝ) (q : B → ℝ) (g : A → B → (I → ℝ)) :
    euclideanEquiv.symm (mixedExpectedPayoff p q g) =
      Blackwell.FiniteApproachability.mixedExpectedPayoff p q
        (fun a b => euclideanEquiv.symm (g a b)) := by
  simp only [mixedExpectedPayoff,
    Blackwell.FiniteApproachability.mixedExpectedPayoff, map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro b hb
  rw [map_expectedPayoff]

/-- Scalar supporting-half-space score computed in finite coordinates. -/
def normalScore {A B I : Type*} [Fintype A] [Fintype B] [Fintype I]
    (g : A → B → (I → ℝ)) (y z : (I → ℝ))
    (p : A → ℝ) (q : B → ℝ) : ℝ :=
  coordinateInner (y - z) (mixedExpectedPayoff p q g)

private theorem normalScore_toCore {A B I : Type*}
    [Fintype A] [Fintype B] [Fintype I]
    (g : A → B → (I → ℝ)) (y z : (I → ℝ))
    (p : A → ℝ) (q : B → ℝ) :
    normalScore g y z p q =
      Blackwell.FiniteApproachability.normalScore
        (fun a b => euclideanEquiv.symm (g a b))
        (euclideanEquiv.symm y) (euclideanEquiv.symm z) p q := by
  unfold normalScore Blackwell.FiniteApproachability.normalScore
  calc
    coordinateInner (y - z) (mixedExpectedPayoff p q g) =
        inner ℝ (euclideanEquiv.symm (y - z))
          (euclideanEquiv.symm (mixedExpectedPayoff p q g)) :=
      coordinateInner_eq_coreInner _ _
    _ = inner ℝ (euclideanEquiv.symm y - euclideanEquiv.symm z)
          (Blackwell.FiniteApproachability.mixedExpectedPayoff p q
            (fun a b => euclideanEquiv.symm (g a b))) := by
      rw [map_sub, map_mixedExpectedPayoff]

/-- Every mixed opponent action admits a feasible mixed response. -/
abbrev mixedBlackwellCondition {A B I : Type*} [Fintype A] [Fintype B]
    [Fintype I] [Nonempty A] [Nonempty B] [Nonempty I]
    (g : A → B → (I → ℝ)) {C : Set (I → ℝ)}
    (hne : C.Nonempty) (hclosed : IsClosed C) (hconvex : Convex ℝ C) : Prop :=
  ∀ y : (I → ℝ), ∀ q : B → ℝ, q ∈ simplexSet B →
    ∃ p : A → ℝ, p ∈ simplexSet A ∧
      normalScore g y (closestPoint hne hclosed hconvex y) p q ≤
        coordinateInner (y - closestPoint hne hclosed hconvex y)
          (closestPoint hne hclosed hconvex y)

/--
Sion minimax turns pointwise feasibility against each opponent mixture into
one player mixture that works against every opponent mixture.
-/
theorem exists_uniform_mixed_response {A B I : Type*}
    [Fintype A] [Fintype B] [Fintype I]
    [Nonempty A] [Nonempty B] [Nonempty I]
    (g : A → B → (I → ℝ))
    (y z : (I → ℝ))
    (hfeasible : ∀ q : B → ℝ, q ∈ simplexSet B →
      ∃ p : A → ℝ, p ∈ simplexSet A ∧
        normalScore g y z p q ≤ coordinateInner (y - z) z) :
    ∃ p : A → ℝ, p ∈ simplexSet A ∧
      ∀ q : B → ℝ, q ∈ simplexSet B →
        normalScore g y z p q ≤ coordinateInner (y - z) z := by
  have hfeasibleCore :
      ∀ q : B → ℝ,
        q ∈ Blackwell.FiniteApproachability.simplexSet B →
        ∃ p : A → ℝ,
          p ∈ Blackwell.FiniteApproachability.simplexSet A ∧
            Blackwell.FiniteApproachability.normalScore
              (fun a b => euclideanEquiv.symm (g a b))
              (euclideanEquiv.symm y) (euclideanEquiv.symm z) p q ≤
                inner ℝ (euclideanEquiv.symm (y - z)) (euclideanEquiv.symm z) := by
    intro q hq
    obtain ⟨p, hp, hscore⟩ := hfeasible q (by
      simpa [simplexSet, simplex,
        Blackwell.FiniteApproachability.simplexSet,
        Blackwell.FiniteApproachability.simplex] using hq)
    refine ⟨p, ?_, ?_⟩
    · simpa [simplexSet, simplex,
        Blackwell.FiniteApproachability.simplexSet,
        Blackwell.FiniteApproachability.simplex] using hp
    · simpa [normalScore_toCore, coordinateInner_eq_coreInner, map_sub] using hscore
  obtain ⟨p, hp, huniform⟩ :=
    Blackwell.FiniteApproachability.exists_uniform_mixed_response
      (E := EuclideanSpace ℝ I)
      (fun a b => euclideanEquiv.symm (g a b))
      (euclideanEquiv.symm y) (euclideanEquiv.symm z) hfeasibleCore
  refine ⟨p, ?_, ?_⟩
  · simpa [simplexSet, simplex,
      Blackwell.FiniteApproachability.simplexSet,
      Blackwell.FiniteApproachability.simplex] using hp
  · intro q hq
    have hq' : q ∈ Blackwell.FiniteApproachability.simplexSet B := by
      simpa [simplexSet, simplex,
        Blackwell.FiniteApproachability.simplexSet,
        Blackwell.FiniteApproachability.simplex] using hq
    have h := huniform q hq'
    simpa [normalScore_toCore, coordinateInner_eq_coreInner, map_sub] using h

/-- Expected running payoff against a pure opponent-action sequence. -/
def adaptiveAverage {I : Type*} [Fintype I]
    (stage : ℕ → (I → ℝ) → (I → ℝ)) :
    ℕ → (I → ℝ)
  | 0 => 0
  | t + 1 => ((t : ℝ) + 1)⁻¹ •
      ((t : ℝ) • adaptiveAverage stage t + stage t (adaptiveAverage stage t))

/-- Average expected payoff against an arbitrary pure opponent sequence. -/
def gameAverage {A B I : Type*} [Fintype A] [Fintype I]
    (g : A → B → (I → ℝ))
    (strategy : (I → ℝ) → {p : A → ℝ // simplex p})
    (opponent : ℕ → B) : ℕ → (I → ℝ) :=
  adaptiveAverage (fun t y => expectedPayoff (strategy y).1 g (opponent t))

private theorem gameAverage_toCore {A B I : Type*}
    [Fintype A] [Fintype B] [Fintype I]
    (g : A → B → (I → ℝ))
    (strategy : (I → ℝ) → {p : A → ℝ // simplex p}) (opponent : ℕ → B) :
    ∀ t, euclideanEquiv.symm (gameAverage g strategy opponent t) =
      Blackwell.FiniteApproachability.gameAverage
        (fun a b => euclideanEquiv.symm (g a b))
        (fun y => strategy (euclideanEquiv y)) opponent t := by
  let stage := fun t y => expectedPayoff (strategy y).1 g (opponent t)
  let stageCore := fun t y =>
    Blackwell.FiniteApproachability.expectedPayoff
      (strategy (euclideanEquiv y)).1
      (fun a b => euclideanEquiv.symm (g a b)) (opponent t)
  change ∀ t, euclideanEquiv.symm (adaptiveAverage stage t) =
    Approachability.adaptiveAverage stageCore t
  intro t
  induction t with
  | zero => simp [adaptiveAverage, Approachability.adaptiveAverage]
  | succ t ih =>
      rw [adaptiveAverage, Approachability.adaptiveAverage]
      rw [map_smul, map_add, map_smul, ih]
      have hstate : adaptiveAverage stage t =
          euclideanEquiv (Approachability.adaptiveAverage stageCore t) := by
        calc
          adaptiveAverage stage t =
              euclideanEquiv (euclideanEquiv.symm (adaptiveAverage stage t)) :=
            (euclideanEquiv.apply_symm_apply _).symm
          _ = euclideanEquiv (Approachability.adaptiveAverage stageCore t) :=
            congrArg euclideanEquiv ih
      have hstage : euclideanEquiv.symm (stage t (adaptiveAverage stage t)) =
          stageCore t (Approachability.adaptiveAverage stageCore t) := by
        rw [hstate]
        dsimp [stage, stageCore]
        exact map_expectedPayoff _ _ _
      rw [hstage]

/-- A forcing response with bounded displacement gives the finite-time rate. -/
theorem finite_game_approachability_bound
    {A B I : Type*} [Fintype A] [Fintype B] [Fintype I]
    [Nonempty A] [Nonempty B] [Nonempty I]
    (g : A → B → (I → ℝ))
    (strategy : (I → ℝ) → {p : A → ℝ // simplex p})
    {C : Set (I → ℝ)}
    (hne : C.Nonempty) (hclosed : IsClosed C) (hconvex : Convex ℝ C)
    (Bnd : ℝ)
    (hforce : ∀ y : (I → ℝ), ∀ b : B,
      coordinateInner (y - closestPoint hne hclosed hconvex y)
        (expectedPayoff (strategy y).1 g b - closestPoint hne hclosed hconvex y) ≤ 0)
    (hbound : ∀ y : (I → ℝ), ∀ b : B,
      coordinateNorm (expectedPayoff (strategy y).1 g b -
        closestPoint hne hclosed hconvex y) ≤ Bnd)
    (hBnd : 0 ≤ Bnd) (opponent : ℕ → B) :
    ∀ {T : ℕ}, 0 < T →
      coordinateInfDist (gameAverage g strategy opponent T) C ≤ Bnd / Real.sqrt T := by
  let gCore := fun a b => euclideanEquiv.symm (g a b)
  let strategyCore := fun y => strategy (euclideanEquiv y)
  let CCore := coreTarget C
  let projCore : EuclideanSpace ℝ I → EuclideanSpace ℝ I := fun y =>
    euclideanEquiv.symm (closestPoint hne hclosed hconvex (euclideanEquiv y))
  have hneCore : CCore.Nonempty := coreTarget_nonempty hne
  have hclosedCore : IsClosed CCore := coreTarget_isClosed hclosed
  have hproj : ∀ y : EuclideanSpace ℝ I, projCore y ∈ CCore := by
    intro y
    change euclideanEquiv (euclideanEquiv.symm
      (closestPoint hne hclosed hconvex (euclideanEquiv y))) ∈ C
    rw [euclideanEquiv.apply_symm_apply]
    exact (closestPoint_spec hne hclosed hconvex (euclideanEquiv y)).1
  have hmin : ∀ y : EuclideanSpace ℝ I, ∀ z ∈ CCore,
      ‖y - projCore y‖ ≤ ‖y - z‖ := by
    intro y z hz
    have hz' : euclideanEquiv z ∈ C := hz
    have hspec := closestPoint_spec hne hclosed hconvex (euclideanEquiv y)
    have hcoord :
        coordinateDistance (euclideanEquiv y)
          (closestPoint hne hclosed hconvex (euclideanEquiv y)) ≤
        coordinateDistance (euclideanEquiv y) (euclideanEquiv z) := by
      calc
        _ = coordinateInfDist (euclideanEquiv y) C := hspec.2.1
        _ = Metric.infDist y CCore := coordinateInfDist_eq_coreInfDist _ _
        _ ≤ dist y z := Metric.infDist_le_dist_of_mem hz
        _ = coordinateDistance (euclideanEquiv y) (euclideanEquiv z) := by
          rw [coordinateDistance_eq_coreDist]
          simp
    simpa [projCore, coordinateDistance_eq_coreDist, dist_eq_norm] using hcoord
  let xCore : ℕ → EuclideanSpace ℝ I := fun t =>
    Blackwell.FiniteApproachability.expectedPayoff
      (strategyCore (Blackwell.FiniteApproachability.gameAverage
        gCore strategyCore opponent t)) gCore (opponent t)
  let avgCore : ℕ → EuclideanSpace ℝ I :=
    Blackwell.FiniteApproachability.gameAverage gCore strategyCore opponent
  have hforceCore : ∀ t : ℕ,
      inner ℝ (avgCore t - projCore (avgCore t))
        (xCore t - projCore (avgCore t)) ≤ 0 := by
    intro t
    have h := hforce (euclideanEquiv (avgCore t)) (opponent t)
    simpa only [xCore, avgCore, projCore, strategyCore, gCore,
      coordinateInner_eq_coreInner, map_sub, euclideanEquiv.symm_apply_apply,
      map_expectedPayoff] using h
  have hboundCore : ∀ t : ℕ,
      ‖xCore t - projCore (avgCore t)‖ ≤ Bnd := by
    intro t
    have h := hbound (euclideanEquiv (avgCore t)) (opponent t)
    simpa only [xCore, avgCore, projCore, strategyCore, gCore,
      coordinateNorm_eq_coreNorm, map_sub, euclideanEquiv.symm_apply_apply,
      map_expectedPayoff] using h
  have havgCore : ∀ t : ℕ,
      ((t : ℝ) + 1) • avgCore (t + 1) = (t : ℝ) • avgCore t + xCore t := by
    intro t
    simpa [avgCore, xCore, Blackwell.FiniteApproachability.gameAverage,
      Blackwell.FiniteApproachability.expectedPayoff] using
      (Approachability.adaptiveAverage_step
        (fun s y => Blackwell.FiniteApproachability.expectedPayoff
          (strategyCore y) gCore (opponent s)) t)
  intro T hT
  have hcore := Approachability.blackwell_approachability_bound
    xCore avgCore (fun t => projCore (avgCore t)) Bnd
    (fun t => hproj (avgCore t))
    (fun t z hz => hmin (avgCore t) z hz)
    havgCore hforceCore hboundCore hBnd (T := T) hT
  rw [coordinateInfDist_eq_coreInfDist, gameAverage_toCore]
  simpa [avgCore, strategyCore, gCore] using hcore

/--
From mixed Blackwell feasibility, bounded payoffs, and a bounded nonempty
closed convex target, a causal mixed strategy achieves the explicit
(G + R) / sqrt(T) expected-average approachability rate.
-/
theorem finite_game_approachability_of_mixedBlackwell
    {A B I : Type*} [Fintype A] [Fintype B] [Fintype I]
    [Nonempty A] [Nonempty B] [Nonempty I]
    (g : A → B → (I → ℝ))
    {C : Set (I → ℝ)}
    (hne : C.Nonempty) (hclosed : IsClosed C) (hconvex : Convex ℝ C)
    (G R : ℝ) (hG : 0 ≤ G) (hR : 0 ≤ R)
    (hpay : ∀ a b, coordinateNorm (g a b) ≤ G)
    (hradius : ∀ z ∈ C, coordinateNorm z ≤ R)
    (hblackwell : mixedBlackwellCondition g hne hclosed hconvex) :
    ∃ strategy : (I → ℝ) → {p : A → ℝ // simplex p},
      ∀ opponent : ℕ → B, ∀ {T : ℕ}, 0 < T →
      coordinateInfDist (gameAverage g strategy opponent T) C ≤
        (G + R) / Real.sqrt T := by
  have hresponse : ∀ y : (I → ℝ),
      ∃ p : A → ℝ, p ∈ simplexSet A ∧
        ∀ b : B,
          coordinateInner (y - closestPoint hne hclosed hconvex y)
            (expectedPayoff p g b - closestPoint hne hclosed hconvex y) ≤ 0 ∧
          coordinateNorm (expectedPayoff p g b -
            closestPoint hne hclosed hconvex y) ≤ G + R := by
    intro y
    let z := closestPoint hne hclosed hconvex y
    have hfeasible : ∀ q : B → ℝ, q ∈ simplexSet B →
        ∃ p : A → ℝ, p ∈ simplexSet A ∧
          normalScore g y z p q ≤ coordinateInner (y - z) z := by
      simpa [z] using hblackwell y
    obtain ⟨p, hp, huniform⟩ := exists_uniform_mixed_response g y z hfeasible
    have hpSimplex : simplex p := hp
    refine ⟨p, hp, ?_⟩
    intro b
    have hq :
        Blackwell.FiniteApproachability.pointMass b ∈ simplexSet B := by
      simpa [simplexSet, simplex,
        Blackwell.FiniteApproachability.simplexSet,
        Blackwell.FiniteApproachability.simplex] using
        (Blackwell.FiniteApproachability.pointMass_mem_simplexSet b)
    have hscore := huniform
      (Blackwell.FiniteApproachability.pointMass b) hq
    have hscore' : coordinateInner (y - z) (expectedPayoff p g b) ≤
        coordinateInner (y - z) z := by
      simpa [normalScore, mixedExpectedPayoff_pointMass] using hscore
    have hforce : coordinateInner (y - z)
        (expectedPayoff p g b - z) ≤ 0 := by
      rw [coordinateInner_sub_right]
      linarith
    have hz : z ∈ C := closestPoint_mem hne hclosed hconvex y
    have hpayCore : ∀ a : A,
        ‖euclideanEquiv.symm (g a b)‖ ≤ G := by
      intro a
      simpa [coordinateNorm_eq_coreNorm] using hpay a b
    have hpayCore' := Blackwell.FiniteApproachability.expectedPayoff_norm_le
      p hpSimplex (fun a b => euclideanEquiv.symm (g a b)) b G hpayCore
    have hpayCoord : coordinateNorm (expectedPayoff p g b) ≤ G := by
      rw [coordinateNorm_eq_coreNorm, map_expectedPayoff]
      exact hpayCore'
    have hnorm : coordinateNorm (expectedPayoff p g b - z) ≤ G + R := by
      calc
        coordinateNorm (expectedPayoff p g b - z) ≤
            coordinateNorm (expectedPayoff p g b) + coordinateNorm z :=
          coordinateNorm_sub_le _ _
        _ ≤ G + R := add_le_add hpayCoord (hradius z hz)
    simpa [z] using And.intro hforce hnorm
  let strategy : (I → ℝ) → {p : A → ℝ // simplex p} := fun y =>
    ⟨Classical.choose (hresponse y), by
      simpa [simplexSet, simplex] using (Classical.choose_spec (hresponse y)).1⟩
  refine ⟨strategy, ?_⟩
  intro opponent T hT
  apply finite_game_approachability_bound g strategy hne hclosed hconvex
    (G + R) ?_ ?_ (add_nonneg hG hR) opponent hT
  · intro y b
    exact ((Classical.choose_spec (hresponse y)).2 b).1
  · intro y b
    exact ((Classical.choose_spec (hresponse y)).2 b).2

end

end Blackwell.FiniteApproachability.Palomar
