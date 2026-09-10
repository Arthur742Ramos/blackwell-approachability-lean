import Mathlib

set_option autoImplicit false

/-!
# Independent statement surface: irreducible improper phi-regret

This Challenge is deliberately Mathlib-only.  It exposes the explicit
three-action comparator family from Section 4.4.1 of Dann, Mansour, Mohri,
Schneider, and Sivan (COLT 2025), together with the paper's canonical
single-invertible-matrix normal form for a prospective reduction to proper
phi-regret.

The selected theorems establish two explicit valid improper phi-regret
families, both canonical-correction obstructions from Section 4.4.1, the
source's finite Equation-(15)-to-(16) and normalized Equation-(16)-to-(17)
bridges, and concrete Equation-(18) vertex/corner membership criteria for
the two cited families: the affine-hyperplane invariant transport of Lemma 4
and the extreme-point, antipodal-displacement obstruction of Lemma 5. The
result proves the finite full-rank-loss-basis implication for the normalized
identity, its implication for the canonical normal form, and the exact
nine- and twelve-constraint specializations of the source's finite-polytope test; it
does not claim to formalize the paper's separate rate/minimality and span
argument that derives Equation (15) from its most general bidirectional
affine definition of linear equivalence, or its general randomized algorithm.
-/

namespace Blackwell.Palomar

open scoped BigOperators Matrix

universe u

/-- Real coordinate vectors for the three-action simplex. -/
abbrev Vec3 := Fin 3 → ℝ

/-- Coordinatewise witness that a three-vector is nonzero.  This explicit
predicate keeps the standalone theorem surface renderer-safe. -/
def nonzeroVec3 (v : Vec3) : Prop := ∃ i, v i ≠ 0

/-- The probability simplex on three actions. -/
def simplex3 : Set Vec3 :=
  {p | (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1}

/-- The three vertices of `simplex3`. -/
def vertex0 : Vec3 := fun i => if i.val = 0 then 1 else 0
def vertex1 : Vec3 := fun i => if i.val = 1 then 1 else 0
def vertex2 : Vec3 := fun i => if i.val = 2 then 1 else 0

/-- The convex family `Id - M_q` of skew-symmetric comparators, where
`q = (a,b,c)` parameterizes
`M_q = [[0,a,-b],[-a,0,c],[b,-c,0]]`. -/
def skewPhi (q p : Vec3) : Vec3 :=
  ![p 0 - q 0 * p 1 + q 1 * p 2,
    p 1 + q 0 * p 0 - q 2 * p 2,
    p 2 - q 1 * p 0 + q 2 * p 1]

/-- The displacement matrix `Id - phi_q` for the skew-simplex family. -/
def skewDisplacementMatrix (q : Vec3) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![0, q 0, -q 1;
     -q 0, 0, q 2;
     q 1, -q 2, 0]

/-- The displacement of an action under a comparator. -/
def displacement (q p : Vec3) : Vec3 := skewPhi q p - p

/-- A vector is common-invariant when it annihilates every comparator
displacement on the action simplex. -/
def commonInvariant (v : Vec3) : Prop :=
  ∀ q ∈ simplex3, ∀ p ∈ simplex3, dotProduct (displacement q p) v = 0

/-- The canonical correction `p + S (phi(p) - p)` used by the source's
linear-equivalence normalization. -/
def corrected (S : Matrix (Fin 3) (Fin 3) ℝ) (q p : Vec3) : Vec3 :=
  p + S *ᵥ displacement q p

/-- `S` makes the whole family proper exactly when all corrected comparators
send the action simplex into itself. -/
def canonicalProper (S : Matrix (Fin 3) (Fin 3) ℝ) : Prop :=
  ∀ q ∈ simplex3, ∀ p ∈ simplex3, corrected S q p ∈ simplex3

/-- A canonical proper reduction requires an invertible correction matrix. -/
def canonicalProperReduction : Prop :=
  ∃ S : Matrix (Fin 3) (Fin 3) ℝ, S.det ≠ 0 ∧ canonicalProper S

/-- The displacement for an arbitrary three-action comparator family. -/
def displacementFor {α : Type u} (φ : α → Vec3 → Vec3) (q : α) (p : Vec3) : Vec3 :=
  φ q p - p

/-- A vector annihilates all displacements in a selected comparator family. -/
def commonInvariantFor {α : Type u} (Q : Set α) (φ : α → Vec3 → Vec3)
    (v : Vec3) : Prop :=
  ∀ q ∈ Q, ∀ p ∈ simplex3, dotProduct (displacementFor φ q p) v = 0

/-- The canonical correction for an arbitrary comparator family. -/
def correctedFor {α : Type u} (φ : α → Vec3 → Vec3)
    (S : Matrix (Fin 3) (Fin 3) ℝ) (q : α) (p : Vec3) : Vec3 :=
  p + S *ᵥ displacementFor φ q p

/-- A single matrix canonically properizes every comparator selected by `Q`. -/
def canonicalProperFor {α : Type u} (Q : Set α) (φ : α → Vec3 → Vec3)
    (S : Matrix (Fin 3) (Fin 3) ℝ) : Prop :=
  ∀ q ∈ Q, ∀ p ∈ simplex3, correctedFor φ S q p ∈ simplex3

/-- A set of three-vectors lies in an affine hyperplane with a nonzero normal. -/
def affineHyperplaneWitness (P : Set Vec3) : Prop :=
  ∃ w : Vec3, ∃ b : ℝ, nonzeroVec3 w ∧
    ∀ p ∈ P, dotProduct p w = b

/-- A vector annihilates all selected comparator displacements on `P`. -/
def commonInvariantOn {α : Type u} (P : Set Vec3) (Q : Set α)
    (φ : α → Vec3 → Vec3) (v : Vec3) : Prop :=
  ∀ q ∈ Q, ∀ p ∈ P, dotProduct (displacementFor φ q p) v = 0

/-- The source's canonical correction maps every selected comparator back
into the action set `P`. -/
def canonicalProperOn {α : Type u} (P : Set Vec3) (Q : Set α)
    (φ : α → Vec3 → Vec3) (S : Matrix (Fin 3) (Fin 3) ℝ) : Prop :=
  ∀ q ∈ Q, ∀ p ∈ P, correctedFor φ S q p ∈ P

/-- Pointwise source notation `M_φ = Id - φ`. -/
def sourceMFor {α : Type u} (φ : α → Vec3 → Vec3) (q : α) (p : Vec3) : Vec3 :=
  p - φ q p

/-- The source's normalized Equation-(16) identity `M_ψ = S M_φ`, after the
comparator correspondence has been fixed. -/
def normalizedMIntertwining {α : Type u} (Q : Set α)
    (φ ψ : α → Vec3 → Vec3) (S : Matrix (Fin 3) (Fin 3) ℝ) : Prop :=
  ∀ q ∈ Q, ∀ p : Vec3, sourceMFor ψ q p = S *ᵥ sourceMFor φ q p

/-- A target comparator family maps every selected action back into its
action set. -/
def properOn {α : Type u} (P : Set Vec3) (Q : Set α)
    (ψ : α → Vec3 → Vec3) : Prop :=
  ∀ q ∈ Q, ∀ p ∈ P, ψ q p ∈ P

/-- The source's normalized proper-reduction form: an invertible `S`, a
proper target family, and the Equation-(16) identity.  This deliberately
does not state the source's full preceding affine-equivalence machinery. -/
def normalizedProperReductionOn {α : Type u} (P : Set Vec3) (Q : Set α)
    (φ : α → Vec3 → Vec3) : Prop :=
  ∃ ψ : α → Vec3 → Vec3, ∃ S : Matrix (Fin 3) (Fin 3) ℝ,
    S.det ≠ 0 ∧ properOn P Q ψ ∧ normalizedMIntertwining Q φ ψ S

/-- The standard basis vectors, which are also the simplex vertices. -/
def basisVector (j : Fin 3) : Vec3 := fun i => if i = j then 1 else 0

/-- A matrix column as a coordinate vector. -/
def matrixColumn (B : Matrix (Fin 3) (Fin 3) ℝ) (j : Fin 3) : Vec3 :=
  fun i => B i j

/-- The action-vertex constraints in Equation (18), for a canonical
correction of a matrix-represented comparator family. -/
def canonicalVertexProperOn {α : Type u} (Q : Set α)
    (φ : α → Vec3 → Vec3) (S : Matrix (Fin 3) (Fin 3) ℝ) : Prop :=
  ∀ q ∈ Q, ∀ j : Fin 3, correctedFor φ S q (basisVector j) ∈ simplex3

/-- The nine action/comparator-vertex constraints for the skew-simplex
family. -/
def skewCanonicalVertexConstraints (S : Matrix (Fin 3) (Fin 3) ℝ) : Prop :=
  ∀ i j : Fin 3, corrected S (basisVector i) (basisVector j) ∈ simplex3

/-- The source's Equation-(15) loss-pairing identity checked at simplex
vertices against a chosen target-loss basis. -/
def lossBasisPairingIntertwining
    (M N S B : Matrix (Fin 3) (Fin 3) ℝ) : Prop :=
  ∀ i j : Fin 3,
    dotProduct (M *ᵥ basisVector j) (S.transpose *ᵥ matrixColumn B i) =
      dotProduct (N *ᵥ basisVector j) (matrixColumn B i)

/-- A comparator family represented by displacement matrices. -/
def matrixComparator {α : Type u} (N : α → Matrix (Fin 3) (Fin 3) ℝ)
    (q : α) (p : Vec3) : Vec3 :=
  p - N q *ᵥ p

/-- A comparator family is represented by its displacement matrices. -/
def matrixComparatorRepresentation {α : Type u}
    (φ : α → Vec3 → Vec3) (M : α → Matrix (Fin 3) (Fin 3) ℝ) : Prop :=
  ∀ q : α, ∀ p : Vec3, φ q p = matrixComparator M q p

/-- Matrix-represented target comparators preserve the action set. -/
def matrixProperOn {α : Type u} (P : Set Vec3) (Q : Set α)
    (N : α → Matrix (Fin 3) (Fin 3) ℝ) : Prop :=
  ∀ q ∈ Q, ∀ p ∈ P, matrixComparator N q p ∈ P

/-- A finite-loss-basis version of the source's normalized proper reduction:
an invertible correction, three independent target losses, a proper matrix
target, and Equation (15) at the simplex vertices. -/
def lossBasisProperReductionOn {α : Type u} (P : Set Vec3) (Q : Set α)
    (M : α → Matrix (Fin 3) (Fin 3) ℝ) : Prop :=
  ∃ N : α → Matrix (Fin 3) (Fin 3) ℝ,
    ∃ S B : Matrix (Fin 3) (Fin 3) ℝ,
      S.det ≠ 0 ∧ B.det ≠ 0 ∧ matrixProperOn P Q N ∧
        ∀ q ∈ Q, lossBasisPairingIntertwining (M q) (N q) S B

/-- The standard convex-combination characterization of an extreme action. -/
def extremePoint (P : Set Vec3) (x : Vec3) : Prop :=
  x ∈ P ∧ ∀ y ∈ P, ∀ z ∈ P, ∀ a b : ℝ,
    0 < a → 0 < b → a + b = 1 →
      x = a • y + b • z → y = x ∧ z = x

/-- Two selected comparators have nonzero antipodal displacements at `x`. -/
def antipodalDisplacements {α : Type u} (Q : Set α) (φ : α → Vec3 → Vec3)
    (x : Vec3) : Prop :=
  ∃ q₁ ∈ Q, ∃ q₂ ∈ Q, ∃ c : ℝ, 0 < c ∧
    nonzeroVec3 (displacementFor φ q₁ x) ∧
      displacementFor φ q₂ x = -(c • displacementFor φ q₁ x)

/-- Fixed points for all selected comparators plus a witnessed escape from the
action set. -/
def validImproperFamily {α : Type u} (P : Set Vec3) (Q : Set α)
    (φ : α → Vec3 → Vec3) : Prop :=
  (∀ q ∈ Q, ∃ p ∈ P, φ q p = p) ∧
    ∃ q ∈ Q, ∃ p ∈ P, φ q p ∉ P

/-- The square of coefficients used in the second explicit source family. -/
def sourceCoefficients : Set (ℝ × ℝ) :=
  {q | -1 ≤ q.1 ∧ q.1 ≤ 1 ∧ -1 ≤ q.2 ∧ q.2 ≤ 1}

/-- First matrix in the second Section 4.4.1 construction. -/
def sourceA : Matrix (Fin 3) (Fin 3) ℝ :=
  !![-6, 8, -9;
      2, -1, -9;
      4, -7, 18]

/-- Second matrix in the second Section 4.4.1 construction. -/
def sourceB : Matrix (Fin 3) (Fin 3) ℝ :=
  !![10, -3, -7;
      6, -6, 10;
      -16, 9, -3]

/-- The source's two-parameter family `Id + a A + b B`. -/
def sourcePhi (q : ℝ × ℝ) (p : Vec3) : Vec3 :=
  p + q.1 • (sourceA *ᵥ p) + q.2 • (sourceB *ᵥ p)

/-- The displacement matrix `Id - phi_(a,b)` for the second family. -/
def sourceDisplacementMatrix (q : ℝ × ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  -(q.1 • sourceA + q.2 • sourceB)

/-- The four coefficient-square corners for the source A/B family. -/
def sourceCorners : Fin 4 → ℝ × ℝ :=
  ![(-1, -1), (-1, 1), (1, -1), (1, 1)]

/-- The twelve action/comparator-corner constraints for the source A/B
coefficient-square family. -/
def sourceABCanonicalCornerConstraints (S : Matrix (Fin 3) (Fin 3) ℝ) : Prop :=
  ∀ i : Fin 4, ∀ j : Fin 3,
    correctedFor sourcePhi S (sourceCorners i) (basisVector j) ∈ simplex3

/-- Every comparator must have a simplex fixed point, while at least one must
escape the simplex, for the family to be valid and improper. -/
def validImproperInstance : Prop :=
  (∀ q ∈ simplex3, ∃ p ∈ simplex3, skewPhi q p = p) ∧
    ∃ q ∈ simplex3, ∃ p ∈ simplex3, skewPhi q p ∉ simplex3

/-- The skew-symmetric family is a valid improper phi-regret instance: every
convexly mixed comparator has a simplex fixed point, but an explicit vertex
comparator sends an allowed action outside the simplex. -/
theorem skewPhi_valid_improper_instance : validImproperInstance := by
  sorry

/-- An invertible canonical properizer of an action set in an affine
hyperplane transports its normal to a nonzero common invariant.  This is the
dimension-three canonical-correction core of Lemma 4 in Dann et al. -/
theorem affine_hyperplane_canonical_properizer_has_nonzero_common_invariant
    {α : Type u} (P : Set Vec3) (Q : Set α) (φ : α → Vec3 → Vec3)
    (S : Matrix (Fin 3) (Fin 3) ℝ) (hdet : S.det ≠ 0)
    (haff : affineHyperplaneWitness P)
    (hproper : canonicalProperOn P Q φ S) :
    ∃ v : Vec3, nonzeroVec3 v ∧ commonInvariantOn P Q φ v := by
  sorry

/-- A proper target satisfying the source's normalized Equation-(16) identity
supplies the canonical properizer in Equation (17). -/
theorem normalized_proper_reduction_implies_canonical_properization
    {α : Type u} (P : Set Vec3) (Q : Set α) (φ ψ : α → Vec3 → Vec3)
    (S : Matrix (Fin 3) (Fin 3) ℝ) (hproper : properOn P Q ψ)
    (hintertwine : normalizedMIntertwining Q φ ψ S) :
    canonicalProperOn P Q φ S := by
  sorry

/-- Equation (15), evaluated at three simplex vertices and a linearly
independent target-loss basis, implies the source's matrix identity
`N = S M` in Equation (16). -/
theorem loss_basis_pairing_implies_normalized_matrix_identity
    (M N S B : Matrix (Fin 3) (Fin 3) ℝ) (hB : B.det ≠ 0)
    (hpair : lossBasisPairingIntertwining M N S B) : N = S * M := by
  sorry

/-- A matrix comparator maps the three-simplex into itself precisely when it
maps the three action vertices into it.  This is the action-vertex half of
the finite-polytope criterion in Equation (18). -/
theorem matrixProperOn_simplex3_iff_on_vertices {α : Type u}
    (Q : Set α) (N : α → Matrix (Fin 3) (Fin 3) ℝ) :
    matrixProperOn simplex3 Q N ↔
      ∀ q ∈ Q, ∀ j : Fin 3, matrixComparator N q (basisVector j) ∈ simplex3 := by
  sorry

/-- Given `M_q = Id - phi_q`, canonical properness on the three-simplex is
equivalent to the action-vertex constraints in Equation (18). -/
theorem canonicalProperOn_simplex3_iff_vertex_constraints
    {α : Type u} (Q : Set α) (φ : α → Vec3 → Vec3)
    (M : α → Matrix (Fin 3) (Fin 3) ℝ)
    (hrepresentation : matrixComparatorRepresentation φ M)
    (S : Matrix (Fin 3) (Fin 3) ℝ) :
    canonicalProperOn simplex3 Q φ S ↔ canonicalVertexProperOn Q φ S := by
  sorry

/-- Canonical-correction core of Lemma 5: an extreme action with antipodal
nonzero comparator displacements rules out every invertible properizer. -/
theorem extreme_antipodal_no_canonical_properizer
    {α : Type u} (P : Set Vec3) (Q : Set α) (φ : α → Vec3 → Vec3) (x : Vec3)
    (hx : extremePoint P x) (hanti : antipodalDisplacements Q φ x) :
    ∀ S : Matrix (Fin 3) (Fin 3) ℝ, S.det ≠ 0 → ¬ canonicalProperOn P Q φ S := by
  sorry

/-- The three skew comparators have no nonzero common invariant vector. -/
theorem skewPhi_has_no_nonzero_common_invariant :
    ¬ ∃ v : Vec3, nonzeroVec3 v ∧ commonInvariant v := by
  sorry

/-- Any canonical correction matrix that maps every comparator back into the
simplex is singular. -/
theorem canonical_proper_matrices_are_singular (S : Matrix (Fin 3) (Fin 3) ℝ)
    (hproper : canonicalProper S) : S.det = 0 := by
  sorry

/-- Consequently the explicit family has no invertible canonical reduction to
proper phi-regret. -/
theorem skewPhi_not_canonically_proper_reducible : ¬ canonicalProperReduction := by
  sorry

/-- For the skew-simplex family, the nine vertex constraints are equivalent
to canonical properness on the full product of the two simplices. -/
theorem skew_canonicalProper_iff_vertex_constraints
    (S : Matrix (Fin 3) (Fin 3) ℝ) :
    canonicalProper S ↔ skewCanonicalVertexConstraints S := by
  sorry

/-- The nine finite vertex constraints for the skew family admit no
invertible correction matrix. -/
theorem skewPhi_no_invertible_nine_vertex_properizer :
    ¬ ∃ S : Matrix (Fin 3) (Fin 3) ℝ,
      S.det ≠ 0 ∧ skewCanonicalVertexConstraints S := by
  sorry

/-- The skew-simplex family has no invertible normalized proper reduction
satisfying the source's Equation-(16) identity. -/
theorem skewPhi_not_normalized_proper_reducible :
    ¬ normalizedProperReductionOn simplex3 simplex3 skewPhi := by
  sorry

/-- The skew-simplex family has no finite-loss-basis Equation-(15) reduction
to a proper matrix comparator family. -/
theorem skewPhi_not_loss_basis_proper_reducible :
    ¬ lossBasisProperReductionOn simplex3 simplex3 skewDisplacementMatrix := by
  sorry

/-- The second explicit Section 4.4.1 family is a valid improper phi-regret
family, with a certified simplex fixed point for every square-bounded pair of
coefficients. -/
theorem sourceAB_valid_improper_family :
    validImproperFamily simplex3 sourceCoefficients sourcePhi := by
  sorry

/-- The all-ones vector remains a nonzero common invariant for the second
family; thus the affine-hyperplane mechanism alone does not exclude it. -/
theorem sourceAB_has_nonzero_common_invariant :
    ∃ v : Vec3, nonzeroVec3 v ∧
      commonInvariantOn simplex3 sourceCoefficients sourcePhi v := by
  sorry

/-- Instantiating the Lemma-5 core shows that the second explicit family has
no invertible canonical reduction to proper phi-regret. -/
theorem sourceAB_not_canonically_proper_reducible :
    ¬ ∃ S : Matrix (Fin 3) (Fin 3) ℝ,
      S.det ≠ 0 ∧ canonicalProperOn simplex3 sourceCoefficients sourcePhi S := by
  sorry

/-- For the source A/B family, the twelve coefficient-corner/action-vertex
constraints are equivalent to canonical properness on the two full polytopes. -/
theorem sourceAB_canonicalProperOn_iff_twelve_corner_constraints
    (S : Matrix (Fin 3) (Fin 3) ℝ) :
    canonicalProperOn simplex3 sourceCoefficients sourcePhi S ↔
      sourceABCanonicalCornerConstraints S := by
  sorry

/-- The twelve finite corner constraints for the source A/B family admit no
invertible correction matrix. -/
theorem sourceAB_no_invertible_twelve_corner_properizer :
    ¬ ∃ S : Matrix (Fin 3) (Fin 3) ℝ,
      S.det ≠ 0 ∧ sourceABCanonicalCornerConstraints S := by
  sorry

/-- The second matrix family has no invertible normalized proper reduction
satisfying the source's Equation-(16) identity. -/
theorem sourceAB_not_normalized_proper_reducible :
    ¬ normalizedProperReductionOn simplex3 sourceCoefficients sourcePhi := by
  sorry

/-- The second matrix family has no finite-loss-basis Equation-(15) reduction
to a proper matrix comparator family. -/
theorem sourceAB_not_loss_basis_proper_reducible :
    ¬ lossBasisProperReductionOn simplex3 sourceCoefficients sourceDisplacementMatrix := by
  sorry

end Blackwell.Palomar
