import Mathlib.Topology.Sion

set_option autoImplicit false

/-
# Minimax-to-response selection

This is the missing bridge between a finite convex game condition and a
single response action.  The input says that every opponent mixed action has
some feasible player response with scalar value at most zero.  Sion's theorem
then supplies one player response that works for every opponent mixed action.
The result is stated for general compact convex action sets so that it can be
reused for finite simplexes and for other convex response models.
-/

namespace Blackwell
namespace Minimax

open Set

theorem exists_uniform_response_of_sion
    {E F : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    {X : Set E} {Y : Set F} (f : E → F → ℝ)
    (ne_X : X.Nonempty) (cX : Convex ℝ X) (kX : IsCompact X)
    (hfy : ∀ y ∈ Y, LowerSemicontinuousOn (fun x => f x y) X)
    (hfy' : ∀ y ∈ Y, QuasiconvexOn ℝ X (fun x => f x y))
    [TopologicalSpace F] [AddCommGroup F] [Module ℝ F]
    [IsTopologicalAddGroup F] [ContinuousSMul ℝ F]
    (cY : Convex ℝ Y) (ne_Y : Y.Nonempty) (kY : IsCompact Y)
    (hfx : ∀ x ∈ X, UpperSemicontinuousOn (fun y => f x y) Y)
    (hfx' : ∀ x ∈ X, QuasiconcaveOn ℝ Y (fun y => f x y))
    (hfeasible : ∀ y ∈ Y, ∃ x ∈ X, f x y ≤ 0) :
    ∃ x ∈ X, ∀ y ∈ Y, f x y ≤ 0 := by
  obtain ⟨a, ha, b, hb, hsaddle⟩ :=
    Sion.exists_isSaddlePointOn ne_X cX kX hfy hfy' cY ne_Y kY hfx hfx'
  obtain ⟨x, hx, hx0⟩ := hfeasible b hb
  have hab : f a b ≤ 0 := (hsaddle x hx b hb).trans hx0
  refine ⟨a, ha, ?_⟩
  intro y hy
  exact (hsaddle a ha y hy).trans hab

end Minimax
end Blackwell
