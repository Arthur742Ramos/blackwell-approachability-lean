import Mathlib

set_option autoImplicit false

/-!
# Independent statement surface: irreducible improper phi-regret

This Challenge is deliberately Mathlib-only.  It exposes the explicit
three-action comparator family from Section 4.4.1 of Dann, Mansour, Mohri,
Schneider, and Sivan (COLT 2025), together with the paper's canonical
single-invertible-matrix normal form for a prospective reduction to proper
phi-regret.

The five selected theorems establish that the family is a valid improper
phi-regret instance; that every invertible canonical properizer of an action
set in real three-space contained in an affine hyperplane induces a nonzero
common invariant; that the explicit skew family has no such invariant;
that every canonical properizing matrix is singular; and therefore that no
invertible canonical proper reduction exists.  The result is scoped to this
canonical normal form; it does not claim to formalize the paper's separate
rate/minimality argument that derives that form from its most general
bidirectional affine definition of linear equivalence.
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

end Blackwell.Palomar
