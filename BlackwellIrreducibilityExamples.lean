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

example : ¬ invertibleTransferProperReductionOn simplex3 simplex3 skewPhi :=
  skewPhi_not_invertible_transfer_proper_reducible

example : ¬ normalizedProperReductionOn simplex3 simplex3 skewPhi :=
  skewPhi_not_normalized_proper_reducible

example : ¬ lossBasisProperReductionOn simplex3 simplex3 skewDisplacementMatrix :=
  skewPhi_not_loss_basis_proper_reducible

example (q : ℝ × ℝ) : ∃ p ∈ simplex3, sourcePhi q p = p :=
  sourcePhi_has_fixed_point q

example : validImproperFamily simplex3 sourceCoefficients sourcePhi :=
  sourceAB_valid_improper_family

example :
    ∃ v : Vec3, nonzeroVec3 v ∧
      commonInvariantOn simplex3 sourceCoefficients sourcePhi v :=
  sourceAB_has_nonzero_common_invariant

example :
    ¬ ∃ S : Matrix (Fin 3) (Fin 3) ℝ,
      S.det ≠ 0 ∧ canonicalProperOn simplex3 sourceCoefficients sourcePhi S :=
  sourceAB_not_canonically_proper_reducible

example :
    ¬ invertibleTransferProperReductionOn simplex3 sourceCoefficients sourcePhi :=
  sourceAB_not_invertible_transfer_proper_reducible

example : ¬ normalizedProperReductionOn simplex3 sourceCoefficients sourcePhi :=
  sourceAB_not_normalized_proper_reducible

example :
    ¬ lossBasisProperReductionOn simplex3 sourceCoefficients sourceDisplacementMatrix :=
  sourceAB_not_loss_basis_proper_reducible

example {α : Type} (P : Set Vec3) (Q : Set α) (φ ψ : α → Vec3 → Vec3)
    (S : Matrix (Fin 3) (Fin 3) ℝ) (hproper : properOn P Q ψ)
    (hintertwine : normalizedMIntertwining Q φ ψ S) :
    canonicalProperOn P Q φ S :=
  normalized_proper_reduction_implies_canonical_properization
    P Q φ ψ S hproper hintertwine

example {α : Type} (P : Set Vec3) (Q : Set α) (φ : α → Vec3 → Vec3)
    (hred : invertibleTransferProperReductionOn P Q φ) :
    ∃ S : Matrix (Fin 3) (Fin 3) ℝ,
      S.det ≠ 0 ∧ canonicalProperOn P Q φ S :=
  invertible_transfer_proper_reduction_implies_canonical_properization
    P Q φ hred

example (M N S B : Matrix (Fin 3) (Fin 3) ℝ) (hB : B.det ≠ 0)
    (hpair : lossBasisPairingIntertwining M N S B) : N = S * M :=
  loss_basis_pairing_implies_normalized_matrix_identity M N S B hB hpair

example {α : Type} (Q : Set α) (N : α → Matrix (Fin 3) (Fin 3) ℝ) :
    matrixProperOn simplex3 Q N ↔
      ∀ q ∈ Q, ∀ j : Fin 3, matrixComparator N q (basisVector j) ∈ simplex3 :=
  matrixProperOn_simplex3_iff_on_vertices Q N

example {α : Type} (Q : Set α) (φ : α → Vec3 → Vec3)
    (M : α → Matrix (Fin 3) (Fin 3) ℝ)
    (hrepresentation : matrixComparatorRepresentation φ M)
    (S : Matrix (Fin 3) (Fin 3) ℝ) :
    canonicalProperOn simplex3 Q φ S ↔ canonicalVertexProperOn Q φ S :=
  canonicalProperOn_simplex3_iff_vertex_constraints Q φ M hrepresentation S

example (S : Matrix (Fin 3) (Fin 3) ℝ) :
    canonicalProper S ↔ skewCanonicalVertexConstraints S :=
  skew_canonicalProper_iff_vertex_constraints S

example : ¬ ∃ S : Matrix (Fin 3) (Fin 3) ℝ,
    S.det ≠ 0 ∧ skewCanonicalVertexConstraints S :=
  skewPhi_no_invertible_nine_vertex_properizer

example (S : Matrix (Fin 3) (Fin 3) ℝ) :
    canonicalProperOn simplex3 sourceCoefficients sourcePhi S ↔
      sourceABCanonicalCornerConstraints S :=
  sourceAB_canonicalProperOn_iff_twelve_corner_constraints S

example : ¬ ∃ S : Matrix (Fin 3) (Fin 3) ℝ,
    S.det ≠ 0 ∧ sourceABCanonicalCornerConstraints S :=
  sourceAB_no_invertible_twelve_corner_properizer

example {α : Type} (P : Set Vec3) (Q : Set α) (φ : α → Vec3 → Vec3)
    (x : Vec3) (hx : extremePoint P x) (hanti : antipodalDisplacements Q φ x)
    (S : Matrix (Fin 3) (Fin 3) ℝ) (hdet : S.det ≠ 0) :
    ¬ canonicalProperOn P Q φ S :=
  extreme_antipodal_no_canonical_properizer P Q φ x hx hanti S hdet

end Blackwell.Irreducibility.Examples
