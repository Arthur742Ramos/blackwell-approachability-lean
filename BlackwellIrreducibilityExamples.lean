import BlackwellIrreducibility

set_option autoImplicit false

/-!
Executable regression checks for the explicit three-action construction.
-/

namespace Blackwell.Irreducibility.Examples

open scoped BigOperators Matrix

example : skewPhi vertex0 vertex1 0 = -1 := by
  norm_num [skewPhi, vertex0, vertex1]

example : skewPhi vertex0 vertex0 1 = 1 := by
  norm_num [skewPhi, vertex0]

example : validImproperInstance :=
  skewPhi_valid_improper_instance

example :
    ¬ ∃ v : Vec3, nonzeroVec3 v ∧ commonInvariant v :=
  skewPhi_has_no_nonzero_common_invariant

example : ¬ canonicalProperReduction :=
  skewPhi_not_canonically_proper_reducible

end Blackwell.Irreducibility.Examples
