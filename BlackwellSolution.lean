import BlackwellIrreducibility

set_option autoImplicit false

/-!
# Proof surface: irreducible improper phi-regret

The declarations below mirror `BlackwellChallenge.lean` exactly.  The checked
proofs are adapters to the independent construction in
`BlackwellIrreducibility.lean`; all names in the public surface remain local
so the Challenge can be rendered without implementation dependencies.
-/

namespace Blackwell.Palomar

open scoped BigOperators Matrix

universe u

abbrev Vec3 := Fin 3 → ℝ

def nonzeroVec3 (v : Vec3) : Prop := ∃ i, v i ≠ 0

def simplex3 : Set Vec3 :=
  {p | (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1}

def vertex0 : Vec3 := fun i => if i.val = 0 then 1 else 0
def vertex1 : Vec3 := fun i => if i.val = 1 then 1 else 0
def vertex2 : Vec3 := fun i => if i.val = 2 then 1 else 0

def skewPhi (q p : Vec3) : Vec3 :=
  ![p 0 - q 0 * p 1 + q 1 * p 2,
    p 1 + q 0 * p 0 - q 2 * p 2,
    p 2 - q 1 * p 0 + q 2 * p 1]

def skewDisplacementMatrix (q : Vec3) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![0, q 0, -q 1;
     -q 0, 0, q 2;
     q 1, -q 2, 0]

def displacement (q p : Vec3) : Vec3 := skewPhi q p - p

def commonInvariant (v : Vec3) : Prop :=
  ∀ q ∈ simplex3, ∀ p ∈ simplex3, dotProduct (displacement q p) v = 0

def corrected (S : Matrix (Fin 3) (Fin 3) ℝ) (q p : Vec3) : Vec3 :=
  p + S *ᵥ displacement q p

def canonicalProper (S : Matrix (Fin 3) (Fin 3) ℝ) : Prop :=
  ∀ q ∈ simplex3, ∀ p ∈ simplex3, corrected S q p ∈ simplex3

def canonicalProperReduction : Prop :=
  ∃ S : Matrix (Fin 3) (Fin 3) ℝ, S.det ≠ 0 ∧ canonicalProper S

def displacementFor {α : Type u} (φ : α → Vec3 → Vec3) (q : α) (p : Vec3) : Vec3 :=
  φ q p - p

def commonInvariantFor {α : Type u} (Q : Set α) (φ : α → Vec3 → Vec3)
    (v : Vec3) : Prop :=
  ∀ q ∈ Q, ∀ p ∈ simplex3, dotProduct (displacementFor φ q p) v = 0

def correctedFor {α : Type u} (φ : α → Vec3 → Vec3)
    (S : Matrix (Fin 3) (Fin 3) ℝ) (q : α) (p : Vec3) : Vec3 :=
  p + S *ᵥ displacementFor φ q p

def canonicalProperFor {α : Type u} (Q : Set α) (φ : α → Vec3 → Vec3)
    (S : Matrix (Fin 3) (Fin 3) ℝ) : Prop :=
  ∀ q ∈ Q, ∀ p ∈ simplex3, correctedFor φ S q p ∈ simplex3

def affineHyperplaneWitness (P : Set Vec3) : Prop :=
  ∃ w : Vec3, ∃ b : ℝ, nonzeroVec3 w ∧
    ∀ p ∈ P, dotProduct p w = b

def commonInvariantOn {α : Type u} (P : Set Vec3) (Q : Set α)
    (φ : α → Vec3 → Vec3) (v : Vec3) : Prop :=
  ∀ q ∈ Q, ∀ p ∈ P, dotProduct (displacementFor φ q p) v = 0

def canonicalProperOn {α : Type u} (P : Set Vec3) (Q : Set α)
    (φ : α → Vec3 → Vec3) (S : Matrix (Fin 3) (Fin 3) ℝ) : Prop :=
  ∀ q ∈ Q, ∀ p ∈ P, correctedFor φ S q p ∈ P

def sourceMFor {α : Type u} (φ : α → Vec3 → Vec3) (q : α) (p : Vec3) : Vec3 :=
  p - φ q p

def normalizedMIntertwining {α : Type u} (Q : Set α)
    (φ ψ : α → Vec3 → Vec3) (S : Matrix (Fin 3) (Fin 3) ℝ) : Prop :=
  ∀ q ∈ Q, ∀ p : Vec3, sourceMFor ψ q p = S *ᵥ sourceMFor φ q p

def properOn {α : Type u} (P : Set Vec3) (Q : Set α)
    (ψ : α → Vec3 → Vec3) : Prop :=
  ∀ q ∈ Q, ∀ p ∈ P, ψ q p ∈ P

def normalizedProperReductionOn {α : Type u} (P : Set Vec3) (Q : Set α)
    (φ : α → Vec3 → Vec3) : Prop :=
  ∃ ψ : α → Vec3 → Vec3, ∃ S : Matrix (Fin 3) (Fin 3) ℝ,
    S.det ≠ 0 ∧ properOn P Q ψ ∧ normalizedMIntertwining Q φ ψ S

def basisVector (j : Fin 3) : Vec3 := fun i => if i = j then 1 else 0

def unitCube3 : Set Vec3 :=
  {l | ∀ i, 0 ≤ l i ∧ l i ≤ 1}

def actionImage (A : Matrix (Fin 3) (Fin 3) ℝ) (P : Set Vec3) : Set Vec3 :=
  {p' | ∃ p ∈ P, p' = A *ᵥ p}

def invertibleTransferProperReductionOn {α : Type u} (P : Set Vec3) (Q : Set α)
    (φ : α → Vec3 → Vec3) : Prop :=
  ∃ (θ : α → Vec3 → Vec3)
    (A Ainv T Tinv : Matrix (Fin 3) (Fin 3) ℝ),
    Ainv * A = 1 ∧ A * Ainv = 1 ∧ Tinv * T = 1 ∧ T * Tinv = 1 ∧
      (∀ q ∈ Q, ∀ p ∈ P, θ q (A *ᵥ p) ∈ actionImage A P) ∧
      ∀ q ∈ Q, ∀ p ∈ P, ∀ l ∈ unitCube3,
        dotProduct (sourceMFor φ q p) l =
          dotProduct (A *ᵥ p - θ q (A *ᵥ p)) (T *ᵥ l)

def matrixColumn (B : Matrix (Fin 3) (Fin 3) ℝ) (j : Fin 3) : Vec3 :=
  fun i => B i j

def canonicalVertexProperOn {α : Type u} (Q : Set α)
    (φ : α → Vec3 → Vec3) (S : Matrix (Fin 3) (Fin 3) ℝ) : Prop :=
  ∀ q ∈ Q, ∀ j : Fin 3, correctedFor φ S q (basisVector j) ∈ simplex3

def skewCanonicalVertexConstraints (S : Matrix (Fin 3) (Fin 3) ℝ) : Prop :=
  ∀ i j : Fin 3, corrected S (basisVector i) (basisVector j) ∈ simplex3

def lossBasisPairingIntertwining
    (M N S B : Matrix (Fin 3) (Fin 3) ℝ) : Prop :=
  ∀ i j : Fin 3,
    dotProduct (M *ᵥ basisVector j) (S.transpose *ᵥ matrixColumn B i) =
      dotProduct (N *ᵥ basisVector j) (matrixColumn B i)

def matrixComparator {α : Type u} (N : α → Matrix (Fin 3) (Fin 3) ℝ)
    (q : α) (p : Vec3) : Vec3 :=
  p - N q *ᵥ p

def matrixComparatorRepresentation {α : Type u}
    (φ : α → Vec3 → Vec3) (M : α → Matrix (Fin 3) (Fin 3) ℝ) : Prop :=
  ∀ q : α, ∀ p : Vec3, φ q p = matrixComparator M q p

def matrixProperOn {α : Type u} (P : Set Vec3) (Q : Set α)
    (N : α → Matrix (Fin 3) (Fin 3) ℝ) : Prop :=
  ∀ q ∈ Q, ∀ p ∈ P, matrixComparator N q p ∈ P

def lossBasisProperReductionOn {α : Type u} (P : Set Vec3) (Q : Set α)
    (M : α → Matrix (Fin 3) (Fin 3) ℝ) : Prop :=
  ∃ N : α → Matrix (Fin 3) (Fin 3) ℝ,
    ∃ S B : Matrix (Fin 3) (Fin 3) ℝ,
      S.det ≠ 0 ∧ B.det ≠ 0 ∧ matrixProperOn P Q N ∧
        ∀ q ∈ Q, lossBasisPairingIntertwining (M q) (N q) S B

def extremePoint (P : Set Vec3) (x : Vec3) : Prop :=
  x ∈ P ∧ ∀ y ∈ P, ∀ z ∈ P, ∀ a b : ℝ,
    0 < a → 0 < b → a + b = 1 →
      x = a • y + b • z → y = x ∧ z = x

def antipodalDisplacements {α : Type u} (Q : Set α) (φ : α → Vec3 → Vec3)
    (x : Vec3) : Prop :=
  ∃ q₁ ∈ Q, ∃ q₂ ∈ Q, ∃ c : ℝ, 0 < c ∧
    nonzeroVec3 (displacementFor φ q₁ x) ∧
      displacementFor φ q₂ x = -(c • displacementFor φ q₁ x)

def validImproperFamily {α : Type u} (P : Set Vec3) (Q : Set α)
    (φ : α → Vec3 → Vec3) : Prop :=
  (∀ q ∈ Q, ∃ p ∈ P, φ q p = p) ∧
    ∃ q ∈ Q, ∃ p ∈ P, φ q p ∉ P

def sourceCoefficients : Set (ℝ × ℝ) :=
  {q | -1 ≤ q.1 ∧ q.1 ≤ 1 ∧ -1 ≤ q.2 ∧ q.2 ≤ 1}

def sourceA : Matrix (Fin 3) (Fin 3) ℝ :=
  !![-6, 8, -9;
      2, -1, -9;
      4, -7, 18]

def sourceB : Matrix (Fin 3) (Fin 3) ℝ :=
  !![10, -3, -7;
      6, -6, 10;
      -16, 9, -3]

def sourcePhi (q : ℝ × ℝ) (p : Vec3) : Vec3 :=
  p + q.1 • (sourceA *ᵥ p) + q.2 • (sourceB *ᵥ p)

def sourceDisplacementMatrix (q : ℝ × ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  -(q.1 • sourceA + q.2 • sourceB)

def sourceCorners : Fin 4 → ℝ × ℝ :=
  ![(-1, -1), (-1, 1), (1, -1), (1, 1)]

def sourceABCanonicalCornerConstraints (S : Matrix (Fin 3) (Fin 3) ℝ) : Prop :=
  ∀ i : Fin 4, ∀ j : Fin 3,
    correctedFor sourcePhi S (sourceCorners i) (basisVector j) ∈ simplex3

def validImproperInstance : Prop :=
  (∀ q ∈ simplex3, ∃ p ∈ simplex3, skewPhi q p = p) ∧
    ∃ q ∈ simplex3, ∃ p ∈ simplex3, skewPhi q p ∉ simplex3

theorem skewPhi_valid_improper_instance : validImproperInstance := by
  simpa [validImproperInstance, simplex3, vertex0, vertex1, vertex2, skewPhi,
    Blackwell.Irreducibility.validImproperInstance,
    Blackwell.Irreducibility.simplex3, Blackwell.Irreducibility.vertex0,
    Blackwell.Irreducibility.vertex1, Blackwell.Irreducibility.vertex2,
    Blackwell.Irreducibility.skewPhi]
    using Blackwell.Irreducibility.skewPhi_valid_improper_instance

theorem affine_hyperplane_canonical_properizer_has_nonzero_common_invariant
    {α : Type u} (P : Set Vec3) (Q : Set α) (φ : α → Vec3 → Vec3)
    (S : Matrix (Fin 3) (Fin 3) ℝ) (hdet : S.det ≠ 0)
    (haff : affineHyperplaneWitness P)
    (hproper : canonicalProperOn P Q φ S) :
    ∃ v : Vec3, nonzeroVec3 v ∧ commonInvariantOn P Q φ v := by
  simpa [nonzeroVec3, affineHyperplaneWitness, commonInvariantOn,
    canonicalProperOn, correctedFor, displacementFor,
    Blackwell.Irreducibility.affineHyperplaneWitness,
    Blackwell.Irreducibility.nonzeroVec3,
    Blackwell.Irreducibility.commonInvariantOn,
    Blackwell.Irreducibility.canonicalProperOn,
    Blackwell.Irreducibility.correctedFor,
    Blackwell.Irreducibility.displacementFor]
    using Blackwell.Irreducibility.affine_hyperplane_canonical_properizer_has_nonzero_common_invariant
      P Q φ S hdet haff hproper

theorem normalized_proper_reduction_implies_canonical_properization
    {α : Type u} (P : Set Vec3) (Q : Set α) (φ ψ : α → Vec3 → Vec3)
    (S : Matrix (Fin 3) (Fin 3) ℝ) (hproper : properOn P Q ψ)
    (hintertwine : normalizedMIntertwining Q φ ψ S) :
    canonicalProperOn P Q φ S := by
  simpa [sourceMFor, normalizedMIntertwining, properOn, canonicalProperOn,
    correctedFor, displacementFor,
    Blackwell.Irreducibility.sourceMFor,
    Blackwell.Irreducibility.normalizedMIntertwining,
    Blackwell.Irreducibility.properOn,
    Blackwell.Irreducibility.canonicalProperOn,
    Blackwell.Irreducibility.correctedFor,
    Blackwell.Irreducibility.displacementFor]
    using Blackwell.Irreducibility.normalized_proper_reduction_implies_canonical_properization
      P Q φ ψ S hproper hintertwine

theorem invertible_transfer_proper_reduction_implies_canonical_properization
    {α : Type u} (P : Set Vec3) (Q : Set α) (φ : α → Vec3 → Vec3)
    (hred : invertibleTransferProperReductionOn P Q φ) :
    ∃ S : Matrix (Fin 3) (Fin 3) ℝ,
      S.det ≠ 0 ∧ canonicalProperOn P Q φ S := by
  change ∃ S : Matrix (Fin 3) (Fin 3) ℝ,
    S.det ≠ 0 ∧ Blackwell.Irreducibility.canonicalProperOn P Q φ S
  exact Blackwell.Irreducibility.invertible_transfer_proper_reduction_implies_canonical_properization
    P Q φ hred

theorem loss_basis_pairing_implies_normalized_matrix_identity
    (M N S B : Matrix (Fin 3) (Fin 3) ℝ) (hB : B.det ≠ 0)
    (hpair : lossBasisPairingIntertwining M N S B) : N = S * M := by
  simpa [basisVector, matrixColumn, lossBasisPairingIntertwining,
    Blackwell.Irreducibility.basisVector,
    Blackwell.Irreducibility.matrixColumn,
    Blackwell.Irreducibility.lossBasisPairingIntertwining]
    using Blackwell.Irreducibility.loss_basis_pairing_implies_normalized_matrix_identity
      M N S B hB hpair

theorem matrixProperOn_simplex3_iff_on_vertices {α : Type u}
    (Q : Set α) (N : α → Matrix (Fin 3) (Fin 3) ℝ) :
    matrixProperOn simplex3 Q N ↔
      ∀ q ∈ Q, ∀ j : Fin 3, matrixComparator N q (basisVector j) ∈ simplex3 := by
  change Blackwell.Irreducibility.matrixProperOn
      Blackwell.Irreducibility.simplex3 Q N ↔
    ∀ q ∈ Q, ∀ j : Fin 3,
      Blackwell.Irreducibility.matrixComparator N q
        (Blackwell.Irreducibility.basisVector j) ∈
          Blackwell.Irreducibility.simplex3
  exact Blackwell.Irreducibility.matrixProperOn_simplex3_iff_on_vertices Q N

theorem canonicalProperOn_simplex3_iff_vertex_constraints
    {α : Type u} (Q : Set α) (φ : α → Vec3 → Vec3)
    (M : α → Matrix (Fin 3) (Fin 3) ℝ)
    (hrepresentation : matrixComparatorRepresentation φ M)
    (S : Matrix (Fin 3) (Fin 3) ℝ) :
    canonicalProperOn simplex3 Q φ S ↔ canonicalVertexProperOn Q φ S := by
  change Blackwell.Irreducibility.canonicalProperOn
      Blackwell.Irreducibility.simplex3 Q φ S ↔
    Blackwell.Irreducibility.canonicalVertexProperOn Q φ S
  exact Blackwell.Irreducibility.canonicalProperOn_simplex3_iff_vertex_constraints
    Q φ M hrepresentation S

theorem extreme_antipodal_no_canonical_properizer
    {α : Type u} (P : Set Vec3) (Q : Set α) (φ : α → Vec3 → Vec3) (x : Vec3)
    (hx : extremePoint P x) (hanti : antipodalDisplacements Q φ x) :
    ∀ S : Matrix (Fin 3) (Fin 3) ℝ, S.det ≠ 0 → ¬ canonicalProperOn P Q φ S := by
  simpa [extremePoint, antipodalDisplacements, nonzeroVec3, canonicalProperOn,
    correctedFor, displacementFor,
    Blackwell.Irreducibility.extremePoint,
    Blackwell.Irreducibility.antipodalDisplacements,
    Blackwell.Irreducibility.nonzeroVec3,
    Blackwell.Irreducibility.canonicalProperOn,
    Blackwell.Irreducibility.correctedFor,
    Blackwell.Irreducibility.displacementFor]
    using Blackwell.Irreducibility.extreme_antipodal_no_canonical_properizer
      P Q φ x hx hanti

theorem skewPhi_has_no_nonzero_common_invariant :
    ¬ ∃ v : Vec3, nonzeroVec3 v ∧ commonInvariant v := by
  simpa [nonzeroVec3, commonInvariant, simplex3, vertex0, vertex1, vertex2,
    displacement, skewPhi,
    Blackwell.Irreducibility.nonzeroVec3,
    Blackwell.Irreducibility.commonInvariant,
    Blackwell.Irreducibility.simplex3, Blackwell.Irreducibility.vertex0,
    Blackwell.Irreducibility.vertex1, Blackwell.Irreducibility.vertex2,
    Blackwell.Irreducibility.displacement,
    Blackwell.Irreducibility.skewPhi]
    using Blackwell.Irreducibility.skewPhi_has_no_nonzero_common_invariant

theorem canonical_proper_matrices_are_singular (S : Matrix (Fin 3) (Fin 3) ℝ)
    (hproper : canonicalProper S) : S.det = 0 := by
  simpa [canonicalProper, simplex3, corrected, displacement, skewPhi,
    Blackwell.Irreducibility.canonicalProper,
    Blackwell.Irreducibility.simplex3, Blackwell.Irreducibility.corrected,
    Blackwell.Irreducibility.displacement,
    Blackwell.Irreducibility.skewPhi]
    using Blackwell.Irreducibility.canonical_proper_matrices_are_singular S hproper

theorem skewPhi_not_canonically_proper_reducible : ¬ canonicalProperReduction := by
  simpa [canonicalProperReduction, canonicalProper, simplex3, corrected,
    displacement, skewPhi,
    Blackwell.Irreducibility.canonicalProperReduction,
    Blackwell.Irreducibility.canonicalProper,
    Blackwell.Irreducibility.simplex3, Blackwell.Irreducibility.corrected,
    Blackwell.Irreducibility.displacement,
    Blackwell.Irreducibility.skewPhi]
    using Blackwell.Irreducibility.skewPhi_not_canonically_proper_reducible

theorem skewPhi_not_invertible_transfer_proper_reducible :
    ¬ invertibleTransferProperReductionOn simplex3 simplex3 skewPhi := by
  change ¬ Blackwell.Irreducibility.invertibleTransferProperReductionOn
    Blackwell.Irreducibility.simplex3 Blackwell.Irreducibility.simplex3
      Blackwell.Irreducibility.skewPhi
  exact Blackwell.Irreducibility.skewPhi_not_invertible_transfer_proper_reducible

theorem skew_canonicalProper_iff_vertex_constraints
    (S : Matrix (Fin 3) (Fin 3) ℝ) :
    canonicalProper S ↔ skewCanonicalVertexConstraints S := by
  change Blackwell.Irreducibility.canonicalProper S ↔
    Blackwell.Irreducibility.skewCanonicalVertexConstraints S
  exact Blackwell.Irreducibility.skew_canonicalProper_iff_vertex_constraints S

theorem skewPhi_no_invertible_nine_vertex_properizer :
    ¬ ∃ S : Matrix (Fin 3) (Fin 3) ℝ,
      S.det ≠ 0 ∧ skewCanonicalVertexConstraints S := by
  change ¬ ∃ S : Matrix (Fin 3) (Fin 3) ℝ,
    S.det ≠ 0 ∧ Blackwell.Irreducibility.skewCanonicalVertexConstraints S
  exact Blackwell.Irreducibility.skewPhi_no_invertible_nine_vertex_properizer

theorem skewPhi_not_normalized_proper_reducible :
    ¬ normalizedProperReductionOn simplex3 simplex3 skewPhi := by
  simpa [normalizedProperReductionOn, normalizedMIntertwining, properOn,
    sourceMFor, simplex3, skewPhi,
    Blackwell.Irreducibility.normalizedProperReductionOn,
    Blackwell.Irreducibility.normalizedMIntertwining,
    Blackwell.Irreducibility.properOn,
    Blackwell.Irreducibility.sourceMFor,
    Blackwell.Irreducibility.simplex3,
    Blackwell.Irreducibility.skewPhi]
    using Blackwell.Irreducibility.skewPhi_not_normalized_proper_reducible

theorem skewPhi_not_loss_basis_proper_reducible :
    ¬ lossBasisProperReductionOn simplex3 simplex3 skewDisplacementMatrix := by
  change ¬ Blackwell.Irreducibility.lossBasisProperReductionOn
    Blackwell.Irreducibility.simplex3 Blackwell.Irreducibility.simplex3
      Blackwell.Irreducibility.skewDisplacementMatrix
  exact Blackwell.Irreducibility.skewPhi_not_loss_basis_proper_reducible

theorem sourceAB_valid_improper_family :
    validImproperFamily simplex3 sourceCoefficients sourcePhi := by
  simpa [validImproperFamily, simplex3, sourceCoefficients, sourcePhi, sourceA,
    sourceB, Blackwell.Irreducibility.validImproperFamily,
    Blackwell.Irreducibility.simplex3,
    Blackwell.Irreducibility.sourceCoefficients,
    Blackwell.Irreducibility.sourcePhi, Blackwell.Irreducibility.sourceA,
    Blackwell.Irreducibility.sourceB]
    using Blackwell.Irreducibility.sourceAB_valid_improper_family

theorem sourceAB_has_nonzero_common_invariant :
    ∃ v : Vec3, nonzeroVec3 v ∧
      commonInvariantOn simplex3 sourceCoefficients sourcePhi v := by
  simpa [nonzeroVec3, commonInvariantOn, simplex3, sourceCoefficients,
    sourcePhi, sourceA, sourceB, displacementFor,
    Blackwell.Irreducibility.nonzeroVec3,
    Blackwell.Irreducibility.commonInvariantOn,
    Blackwell.Irreducibility.simplex3,
    Blackwell.Irreducibility.sourceCoefficients,
    Blackwell.Irreducibility.sourcePhi, Blackwell.Irreducibility.sourceA,
    Blackwell.Irreducibility.sourceB,
    Blackwell.Irreducibility.displacementFor]
    using Blackwell.Irreducibility.sourceAB_has_nonzero_common_invariant

theorem sourceAB_not_canonically_proper_reducible :
    ¬ ∃ S : Matrix (Fin 3) (Fin 3) ℝ,
      S.det ≠ 0 ∧ canonicalProperOn simplex3 sourceCoefficients sourcePhi S := by
  simpa [canonicalProperOn, correctedFor, displacementFor, simplex3,
    sourceCoefficients, sourcePhi, sourceA, sourceB,
    Blackwell.Irreducibility.canonicalProperOn,
    Blackwell.Irreducibility.correctedFor,
    Blackwell.Irreducibility.displacementFor,
    Blackwell.Irreducibility.simplex3,
    Blackwell.Irreducibility.sourceCoefficients,
    Blackwell.Irreducibility.sourcePhi, Blackwell.Irreducibility.sourceA,
    Blackwell.Irreducibility.sourceB]
    using Blackwell.Irreducibility.sourceAB_not_canonically_proper_reducible

theorem sourceAB_not_invertible_transfer_proper_reducible :
    ¬ invertibleTransferProperReductionOn simplex3 sourceCoefficients sourcePhi := by
  change ¬ Blackwell.Irreducibility.invertibleTransferProperReductionOn
    Blackwell.Irreducibility.simplex3 Blackwell.Irreducibility.sourceCoefficients
      Blackwell.Irreducibility.sourcePhi
  exact Blackwell.Irreducibility.sourceAB_not_invertible_transfer_proper_reducible

theorem sourceAB_canonicalProperOn_iff_twelve_corner_constraints
    (S : Matrix (Fin 3) (Fin 3) ℝ) :
    canonicalProperOn simplex3 sourceCoefficients sourcePhi S ↔
      sourceABCanonicalCornerConstraints S := by
  change Blackwell.Irreducibility.canonicalProperOn
      Blackwell.Irreducibility.simplex3
      Blackwell.Irreducibility.sourceCoefficients
      Blackwell.Irreducibility.sourcePhi S ↔
    Blackwell.Irreducibility.sourceABCanonicalCornerConstraints S
  exact Blackwell.Irreducibility.sourceAB_canonicalProperOn_iff_twelve_corner_constraints S

theorem sourceAB_no_invertible_twelve_corner_properizer :
    ¬ ∃ S : Matrix (Fin 3) (Fin 3) ℝ,
      S.det ≠ 0 ∧ sourceABCanonicalCornerConstraints S := by
  change ¬ ∃ S : Matrix (Fin 3) (Fin 3) ℝ,
    S.det ≠ 0 ∧ Blackwell.Irreducibility.sourceABCanonicalCornerConstraints S
  exact Blackwell.Irreducibility.sourceAB_no_invertible_twelve_corner_properizer

theorem sourceAB_not_normalized_proper_reducible :
    ¬ normalizedProperReductionOn simplex3 sourceCoefficients sourcePhi := by
  simpa [normalizedProperReductionOn, normalizedMIntertwining, properOn,
    sourceMFor, simplex3, sourceCoefficients, sourcePhi, sourceA, sourceB,
    Blackwell.Irreducibility.normalizedProperReductionOn,
    Blackwell.Irreducibility.normalizedMIntertwining,
    Blackwell.Irreducibility.properOn,
    Blackwell.Irreducibility.sourceMFor,
    Blackwell.Irreducibility.simplex3,
    Blackwell.Irreducibility.sourceCoefficients,
    Blackwell.Irreducibility.sourcePhi, Blackwell.Irreducibility.sourceA,
    Blackwell.Irreducibility.sourceB]
    using Blackwell.Irreducibility.sourceAB_not_normalized_proper_reducible

theorem sourceAB_not_loss_basis_proper_reducible :
    ¬ lossBasisProperReductionOn simplex3 sourceCoefficients sourceDisplacementMatrix := by
  change ¬ Blackwell.Irreducibility.lossBasisProperReductionOn
    Blackwell.Irreducibility.simplex3 Blackwell.Irreducibility.sourceCoefficients
      Blackwell.Irreducibility.sourceDisplacementMatrix
  exact Blackwell.Irreducibility.sourceAB_not_loss_basis_proper_reducible

end Blackwell.Palomar
