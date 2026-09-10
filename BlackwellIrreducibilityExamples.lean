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

example (S : Matrix (Fin 3) (Fin 3) ℝ) (hdet : S.det ≠ 0)
    (hproper : canonicalProperFor simplex3 skewPhi S) :
    ∃ v : Vec3, nonzeroVec3 v ∧ commonInvariantFor simplex3 skewPhi v :=
  canonical_properizer_has_nonzero_common_invariant simplex3 skewPhi S hdet hproper

example (S : Matrix (Fin 3) (Fin 3) ℝ) (hdet : S.det ≠ 0)
    (hproper : canonicalProperOn simplex3 simplex3 skewPhi S) :
    ∃ v : Vec3, nonzeroVec3 v ∧ commonInvariantOn simplex3 simplex3 skewPhi v :=
  affine_hyperplane_canonical_properizer_has_nonzero_common_invariant
    simplex3 simplex3 skewPhi S hdet simplex3_affineHyperplaneWitness hproper

example :
    ¬ ∃ v : Vec3, nonzeroVec3 v ∧ commonInvariant v :=
  skewPhi_has_no_nonzero_common_invariant

example : ¬ canonicalProperReduction :=
  skewPhi_not_canonically_proper_reducible

end Blackwell.Irreducibility.Examples
