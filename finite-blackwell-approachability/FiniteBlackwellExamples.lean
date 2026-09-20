import FiniteBlackwellSolution

set_option autoImplicit false

namespace Blackwell.FiniteApproachability.Palomar.Examples

open Set
open scoped BigOperators

noncomputable section

/-- A two-action zero-sum game with scalar vector payoff. -/
def matchingPenniesPayoff (a b : Bool) : FiniteEuclideanSpace Unit :=
  fun _ => if a = b then 1 else -1

/-- The uniform mixed action on the two player actions. -/
def uniform : Bool → ℝ := fun _ => (1 / 2 : ℝ)

lemma uniform_mem_simplex : simplex uniform := by
  constructor
  · intro a
    norm_num [uniform]
  · simp [uniform]

lemma uniform_expectedPayoff (b : Bool) :
    expectedPayoff uniform matchingPenniesPayoff b = 0 := by
  cases b <;> ext i <;>
    norm_num [expectedPayoff, matchingPenniesPayoff, uniform]

/--
The mixed-Blackwell hypothesis holds for matching pennies and the singleton
target {0}: the uniform player mixture has expected payoff zero against every
opponent mixture.
-/
lemma matchingPennies_blackwell :
    mixedBlackwellCondition matchingPenniesPayoff
      (C := ({0} : Set (FiniteEuclideanSpace Unit))) (by simp) isClosed_singleton
      (convex_singleton (0 : FiniteEuclideanSpace Unit)) := by
  have hne : ({0} : Set (FiniteEuclideanSpace Unit)).Nonempty := ⟨0, by simp⟩
  intro y q hq
  have hz : closestPoint hne isClosed_singleton
      (convex_singleton (0 : FiniteEuclideanSpace Unit)) y = 0 := by
    have hmem := closestPoint_mem hne isClosed_singleton
      (convex_singleton (0 : FiniteEuclideanSpace Unit)) y
    simpa using hmem
  refine ⟨uniform, uniform_mem_simplex, ?_⟩
  rw [hz]
  simp [normalScore, coordinateInner, mixedExpectedPayoff,
    uniform_expectedPayoff]

/--
The general theorem yields an explicit finite-time expected-distance bound in
matching pennies. This is an expectation guarantee for mixed play, not a
pathwise claim about independently sampled realized payoffs.
-/
example :
    ∃ strategy : FiniteEuclideanSpace Unit → Mixed Bool,
      ∀ opponent : ℕ → Bool, ∀ {T : ℕ}, 0 < T →
      coordinateInfDist (gameAverage matchingPenniesPayoff strategy opponent T)
        ({0} : Set (FiniteEuclideanSpace Unit)) ≤ (1 + 0) / Real.sqrt T := by
  have hne : ({0} : Set (FiniteEuclideanSpace Unit)).Nonempty := ⟨0, by simp⟩
  have hclosed : IsClosed ({0} : Set (FiniteEuclideanSpace Unit)) := isClosed_singleton
  have hconvex : Convex ℝ ({0} : Set (FiniteEuclideanSpace Unit)) :=
    convex_singleton 0
  apply finite_game_approachability_of_mixedBlackwell
    (g := matchingPenniesPayoff)
    (C := ({0} : Set (FiniteEuclideanSpace Unit))) hne hclosed hconvex
    1 0 (by norm_num) (by norm_num)
  · intro a b
    cases a <;> cases b <;>
      norm_num [matchingPenniesPayoff, coordinateNorm]
  · intro z hz
    have : z = 0 := by simpa using hz
    simp [this, coordinateNorm]
  · exact matchingPennies_blackwell

end

end Blackwell.FiniteApproachability.Palomar.Examples
