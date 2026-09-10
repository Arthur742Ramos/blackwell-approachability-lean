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

theorem canonical_proper_has_nonzero_common_invariant
    (S : Matrix (Fin 3) (Fin 3) ℝ) (hdet : S.det ≠ 0)
    (hproper : canonicalProper S) :
    ∃ v : Vec3, nonzeroVec3 v ∧ commonInvariant v := by
  simpa [nonzeroVec3, commonInvariant, canonicalProper, simplex3, corrected,
    displacement, skewPhi,
    Blackwell.Irreducibility.canonicalProper,
    Blackwell.Irreducibility.nonzeroVec3,
    Blackwell.Irreducibility.commonInvariant,
    Blackwell.Irreducibility.simplex3, Blackwell.Irreducibility.corrected,
    Blackwell.Irreducibility.displacement,
    Blackwell.Irreducibility.skewPhi]
    using Blackwell.Irreducibility.canonical_proper_has_nonzero_common_invariant
      S hdet hproper

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

end Blackwell.Palomar
