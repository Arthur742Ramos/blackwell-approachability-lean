import RateReductionSolution

set_option autoImplicit false

/-!
# Concrete finite two-by-two instance

This small instance exercises the public theorem surface with two constraints,
two actions, and one loss coordinate.  It is intentionally a validation
example, not a separate claimed learning-theory result.
-/

namespace Blackwell.RateReduction.Palomar.Examples

open scoped BigOperators

noncomputable section

abbrev Two := Fin 2
abbrev One := Fin 1

def uniformTwo : Mixed Two :=
  ⟨fun _ => (1 : ℝ) / 2, by
    constructor
    · intro i
      norm_num
    · norm_num [Fin.sum_univ_two]⟩

/-- Two opposite finite constraint coordinates. -/
def toyPayoff : Payoff Two Two One :=
  fun i j _ => if i = j then 1 else -1

example : FiniteTensorTightReduction toyPayoff uniformTwo :=
  finiteTensorTightReduction_of_anchor toyPayoff uniformTwo

example : AlgorithmicFiniteTensorTightReduction toyPayoff uniformTwo :=
  algorithmicFiniteTensorTightReduction_of_anchor toyPayoff uniformTwo

example (w : Mixed Two) (x : JointMixed Two Two) :
    ¬ jointSimplex (shift w.1 x.1) :=
  shift_is_improper w x

example {T : ℕ} (p : Fin T → Mixed Two) (l : Fin T → Dist One) :
    regretLoss toyPayoff (liftTrajectory uniformTwo p) l = approachLoss toyPayoff p l := by
  exact approach_to_regret_exact toyPayoff uniformTwo p l

end

end Blackwell.RateReduction.Palomar.Examples
