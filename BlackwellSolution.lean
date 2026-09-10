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

end Blackwell.Palomar
