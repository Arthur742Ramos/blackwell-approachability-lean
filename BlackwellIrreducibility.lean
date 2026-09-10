import Mathlib

set_option autoImplicit false

/-!
# An irreducible improper phi-regret family

This module formalizes the explicit three-action construction in Section 4.4.1
of Dann, Mansour, Mohri, Schneider, and Sivan, *Rate-Preserving Reductions for
Blackwell Approachability* (COLT 2025).  The action set is the three-simplex.
The benchmark family is the convex hull of three improper linear maps arising
from three-by-three skew-symmetric matrices.

The paper's normal form for a prospective linear reduction to proper
phi-regret has the shape

```
p |-> p + S (phi(p) - p)
```

with an invertible correction matrix `S`.  The selected result proves that no
such matrix can make every member of this family proper.  The formalization is
intentionally scoped to that canonical normal form; it does not formalize the
paper's separate rate/minimality machinery used to obtain the normal form from
its most general bidirectional affine definition of linear equivalence.
-/

namespace Blackwell.Irreducibility

open scoped BigOperators Matrix

universe u

/-- Real coordinate vectors for the three-action simplex. -/
abbrev Vec3 := Fin 3 → ℝ

/-- Coordinatewise witness that a three-vector is nonzero.  Keeping this
predicate explicit makes the public theorem boundary independent of the
renderer's function-space zero notation. -/
def nonzeroVec3 (v : Vec3) : Prop := ∃ i, v i ≠ 0

/-- The probability simplex on three actions. -/
def simplex3 : Set Vec3 :=
  {p | (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1}

/-- The three simplex vertices.  Defining coordinates through `Fin.val` keeps
    the concrete calculation robust under finite-index normalization. -/
def vertex0 : Vec3 := fun i => if i.val = 0 then 1 else 0
def vertex1 : Vec3 := fun i => if i.val = 1 then 1 else 0
def vertex2 : Vec3 := fun i => if i.val = 2 then 1 else 0

/-- The convex family of comparator maps.  For coefficients
`q = (a,b,c)`, this is `Id - M_q`, where
`M_q = [[0,a,-b],[-a,0,c],[b,-c,0]]`. -/
def skewPhi (q p : Vec3) : Vec3 :=
  ![p 0 - q 0 * p 1 + q 1 * p 2,
    p 1 + q 0 * p 0 - q 2 * p 2,
    p 2 - q 1 * p 0 + q 2 * p 1]

/-- The displacement of an action under a comparator.  Naming it keeps the
public invariant statements independent of function-space subtraction
notation. -/
def displacement (q p : Vec3) : Vec3 := skewPhi q p - p

/-- A vector is common-invariant when it annihilates every comparator
displacement on the action simplex. -/
def commonInvariant (v : Vec3) : Prop :=
  ∀ q ∈ simplex3, ∀ p ∈ simplex3, dotProduct (displacement q p) v = 0

/-- The canonical correction used after the paper's linear-equivalence
normalization. -/
def corrected (S : Matrix (Fin 3) (Fin 3) ℝ) (q p : Vec3) : Vec3 :=
  p + S *ᵥ displacement q p

/-- A matrix makes the entire comparator family proper in the canonical
normal form precisely when each corrected map sends the simplex to itself. -/
def canonicalProper (S : Matrix (Fin 3) (Fin 3) ℝ) : Prop :=
  ∀ q ∈ simplex3, ∀ p ∈ simplex3, corrected S q p ∈ simplex3

/-- A canonical proper reduction additionally requires the correction matrix
to be invertible.  Over `ℝ^3` this is `S.det ≠ 0`. -/
def canonicalProperReduction : Prop :=
  ∃ S : Matrix (Fin 3) (Fin 3) ℝ, S.det ≠ 0 ∧ canonicalProper S

/-- The displacement for an arbitrary three-action comparator family.  The
family index need not itself be a simplex: `Q` below selects the comparators
whose common properization is under consideration. -/
def displacementFor {α : Type u} (φ : α → Vec3 → Vec3) (q : α) (p : Vec3) : Vec3 :=
  φ q p - p

/-- A vector annihilates all displacements of a selected comparator family. -/
def commonInvariantFor {α : Type u} (Q : Set α) (φ : α → Vec3 → Vec3)
    (v : Vec3) : Prop :=
  ∀ q ∈ Q, ∀ p ∈ simplex3, dotProduct (displacementFor φ q p) v = 0

/-- The source's canonical correction for an arbitrary comparator family. -/
def correctedFor {α : Type u} (φ : α → Vec3 → Vec3)
    (S : Matrix (Fin 3) (Fin 3) ℝ) (q : α) (p : Vec3) : Vec3 :=
  p + S *ᵥ displacementFor φ q p

/-- A single matrix canonically properizes every comparator selected by `Q`. -/
def canonicalProperFor {α : Type u} (Q : Set α) (φ : α → Vec3 → Vec3)
    (S : Matrix (Fin 3) (Fin 3) ℝ) : Prop :=
  ∀ q ∈ Q, ∀ p ∈ simplex3, correctedFor φ S q p ∈ simplex3

/-- A set of three-vectors lies in an affine hyperplane with a specified
normal.  This is the geometric hypothesis used in Lemma 4 of the source:
the action set need not be the simplex. -/
def affineHyperplaneWitness (P : Set Vec3) : Prop :=
  ∃ w : Vec3, ∃ b : ℝ, nonzeroVec3 w ∧
    ∀ p ∈ P, dotProduct p w = b

/-- A vector annihilates all comparator displacements on an arbitrary action
set `P`. -/
def commonInvariantOn {α : Type u} (P : Set Vec3) (Q : Set α)
    (φ : α → Vec3 → Vec3) (v : Vec3) : Prop :=
  ∀ q ∈ Q, ∀ p ∈ P, dotProduct (displacementFor φ q p) v = 0

/-- A canonical correction maps every selected comparator back into an
arbitrary action set `P`. -/
def canonicalProperOn {α : Type u} (P : Set Vec3) (Q : Set α)
    (φ : α → Vec3 → Vec3) (S : Matrix (Fin 3) (Fin 3) ℝ) : Prop :=
  ∀ q ∈ Q, ∀ p ∈ P, correctedFor φ S q p ∈ P

/-- The standard convex-combination characterization of an extreme point of
an action set.  It is stated locally so the public obstruction theorem has a
small, explicit hypothesis. -/
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

/-- Every comparator has a simplex fixed point and some comparator sends a
simplex point outside it, the defining features of this improper phi-regret
family. -/
def validImproperInstance : Prop :=
  (∀ q ∈ simplex3, ∃ p ∈ simplex3, skewPhi q p = p) ∧
    ∃ q ∈ simplex3, ∃ p ∈ simplex3, skewPhi q p ∉ simplex3

/-- The fixed-point and escape conditions for an arbitrary selected comparator
family on an arbitrary action set. -/
def validImproperFamily {α : Type u} (P : Set Vec3) (Q : Set α)
    (φ : α → Vec3 → Vec3) : Prop :=
  (∀ q ∈ Q, ∃ p ∈ P, φ q p = p) ∧
    ∃ q ∈ Q, ∃ p ∈ P, φ q p ∉ P

/-- The coefficient square used for the second irreducible source family. -/
def sourceCoefficients : Set (ℝ × ℝ) :=
  {q | -1 ≤ q.1 ∧ q.1 ≤ 1 ∧ -1 ≤ q.2 ∧ q.2 ≤ 1}

/-- The first matrix in the second construction of Dann et al., Section 4.4.1. -/
def sourceA : Matrix (Fin 3) (Fin 3) ℝ :=
  !![-6, 8, -9;
      2, -1, -9;
      4, -7, 18]

/-- The second matrix in the second construction of Dann et al., Section 4.4.1. -/
def sourceB : Matrix (Fin 3) (Fin 3) ℝ :=
  !![10, -3, -7;
      6, -6, 10;
      -16, 9, -3]

/-- The source's two-parameter family `Id + a A + b B`. -/
def sourcePhi (q : ℝ × ℝ) (p : Vec3) : Vec3 :=
  p + q.1 • (sourceA *ᵥ p) + q.2 • (sourceB *ᵥ p)

/-- A homogeneous right-kernel certificate for `a A + b B`. -/
def sourceKernel (a b : ℝ) : Vec3 :=
  ![81 * a^2 - 46 * a * b + 72 * b^2,
    2 * (36 * a^2 - 41 * a * b + 71 * b^2),
    2 * (5 * a^2 + 8 * a * b + 21 * b^2)]

/-- The mass used to normalize `sourceKernel` to a simplex point. -/
def sourceKernelMass (a b : ℝ) : ℝ :=
  163 * a^2 - 112 * a * b + 256 * b^2

lemma sum_fin3 (f : Fin 3 → ℝ) : ∑ i, f i = f 0 + f 1 + f 2 := by
  rw [Fin.sum_univ_succ]
  rw [Fin.sum_univ_succ]
  rw [Fin.sum_univ_succ]
  simp [add_assoc]

lemma sourceKernelMass_eq_sum (a b : ℝ) :
    ∑ i, sourceKernel a b i = sourceKernelMass a b := by
  rw [sum_fin3]
  simp [sourceKernel, sourceKernelMass]
  ring

lemma sourceKernel_nonnegative (a b : ℝ) (i : Fin 3) :
    0 ≤ sourceKernel a b i := by
  fin_cases i
  · change 0 ≤ 81 * a ^ 2 - 46 * a * b + 72 * b ^ 2
    have h : 324 * (81 * a ^ 2 - 46 * a * b + 72 * b ^ 2) =
        (162 * a - 46 * b) ^ 2 + 21212 * b ^ 2 := by
      ring
    nlinarith [sq_nonneg (162 * a - 46 * b), sq_nonneg b]
  · change 0 ≤ 2 * (36 * a ^ 2 - 41 * a * b + 71 * b ^ 2)
    have h : 144 * (36 * a ^ 2 - 41 * a * b + 71 * b ^ 2) =
        (72 * a - 41 * b) ^ 2 + 8543 * b ^ 2 := by
      ring
    nlinarith [sq_nonneg (72 * a - 41 * b), sq_nonneg b]
  · change 0 ≤ 2 * (5 * a ^ 2 + 8 * a * b + 21 * b ^ 2)
    have h : 20 * (5 * a ^ 2 + 8 * a * b + 21 * b ^ 2) =
        (10 * a + 8 * b) ^ 2 + 356 * b ^ 2 := by
      ring
    nlinarith [sq_nonneg (10 * a + 8 * b), sq_nonneg b]

lemma sourceKernelMass_pos (a b : ℝ) (hzero : a ≠ 0 ∨ b ≠ 0) :
    0 < sourceKernelMass a b := by
  have h : 652 * sourceKernelMass a b =
      (326 * a - 112 * b) ^ 2 + 154368 * b ^ 2 := by
    simp [sourceKernelMass]
    ring
  have hnonneg : 0 ≤ sourceKernelMass a b := by
    nlinarith [sq_nonneg (326 * a - 112 * b), sq_nonneg b]
  by_contra hpos
  have hle : sourceKernelMass a b ≤ 0 := le_of_not_gt hpos
  have hmasszero : sourceKernelMass a b = 0 := by linarith
  have hsumzero : (326 * a - 112 * b) ^ 2 + 154368 * b ^ 2 = 0 := by
    nlinarith [h]
  have hbzero : b = 0 := by
    nlinarith [sq_nonneg (326 * a - 112 * b)]
  have hazero : a = 0 := by
    rw [hbzero] at hsumzero
    nlinarith
  exact hzero.elim (fun ha => ha hazero) (fun hb => hb hbzero)

lemma sourcePhi_smul (q : ℝ × ℝ) (r : ℝ) (p : Vec3) :
    sourcePhi q (r • p) = r • sourcePhi q p := by
  ext i
  simp [sourcePhi, Matrix.mulVec_smul]
  ring

lemma sourcePhi_sourceKernel (a b : ℝ) :
    sourcePhi (a, b) (sourceKernel a b) = sourceKernel a b := by
  ext i
  fin_cases i <;>
    norm_num [sourcePhi, sourceA, sourceB, sourceKernel, Matrix.mulVec,
      dotProduct, Fin.sum_univ_succ, Matrix.of_apply, Matrix.cons_val',
      Matrix.head_cons, Matrix.tail_cons, Matrix.vecHead, Matrix.vecTail,
      Matrix.cons_val_one, Matrix.cons_val_two, Pi.smul_apply,
      Function.comp_apply] <;>
    ring

lemma sourcePhi_has_fixed_point (q : ℝ × ℝ) :
    ∃ p ∈ simplex3, sourcePhi q p = p := by
  rcases q with ⟨a, b⟩
  by_cases habzero : a = 0 ∧ b = 0
  · rcases habzero with ⟨rfl, rfl⟩
    refine ⟨vertex0, ?_, ?_⟩
    · constructor
      · intro i
        fin_cases i <;> norm_num [vertex0]
      · rw [sum_fin3]
        norm_num [vertex0]
    simp [sourcePhi]
  · have hnonzero : a ≠ 0 ∨ b ≠ 0 := by
      by_contra h
      push Not at h
      exact habzero ⟨h.1, h.2⟩
    let k : Vec3 := sourceKernel a b
    let m : ℝ := sourceKernelMass a b
    have hm : 0 < m := by
      simpa [m] using sourceKernelMass_pos a b hnonzero
    have hk : ∀ i, 0 ≤ k i := by
      intro i
      simpa [k] using sourceKernel_nonnegative a b i
    have hsum : ∑ i, k i = m := by
      simpa [k, m] using sourceKernelMass_eq_sum a b
    let p : Vec3 := fun i => k i / m
    have hp : p ∈ simplex3 := by
      constructor
      · intro i
        exact div_nonneg (hk i) (le_of_lt hm)
      · rw [sum_fin3]
        have hsum3 : k 0 + k 1 + k 2 = m := by
          rw [← sum_fin3]
          exact hsum
        dsimp [p]
        field_simp [ne_of_gt hm]
        linarith
    refine ⟨p, hp, ?_⟩
    have hkfixed : sourcePhi (a, b) k = k := by
      simpa [k] using sourcePhi_sourceKernel a b
    have hp_eq : p = m⁻¹ • k := by
      ext i
      simp [p, div_eq_mul_inv, mul_comm]
    calc
      sourcePhi (a, b) p = sourcePhi (a, b) (m⁻¹ • k) := by rw [hp_eq]
      _ = m⁻¹ • sourcePhi (a, b) k := sourcePhi_smul (a, b) m⁻¹ k
      _ = m⁻¹ • k := by rw [hkfixed]
      _ = p := hp_eq.symm

/-- The two-parameter source family is genuinely improper: the comparator
with coefficients `(1, 0)` takes the first simplex vertex outside the
simplex. -/
lemma sourcePhi_is_improper :
    ∃ q ∈ sourceCoefficients, ∃ p ∈ simplex3, sourcePhi q p ∉ simplex3 := by
  refine ⟨(1, 0), ?_, vertex0, ?_, ?_⟩
  · norm_num [sourceCoefficients]
  · constructor
    · intro i
      fin_cases i <;> norm_num [vertex0]
    · rw [sum_fin3]
      norm_num [vertex0]
  · intro hmem
    have hnonneg := hmem.1 0
    norm_num [sourcePhi, sourceA, sourceB, vertex0, Matrix.mulVec,
      dotProduct, Fin.sum_univ_succ, Matrix.of_apply, Matrix.cons_val',
      Matrix.head_cons, Matrix.tail_cons, Matrix.vecHead, Matrix.vecTail,
      Matrix.cons_val_one, Matrix.cons_val_two, Pi.smul_apply,
      Function.comp_apply] at hnonneg

/-- The source's second three-action family is a valid improper phi-regret
family: every selected comparator has a simplex fixed point, but one explicit
comparator is not simplex preserving. -/
theorem sourceAB_valid_improper_family :
    validImproperFamily simplex3 sourceCoefficients sourcePhi := by
  constructor
  · intro q _
    exact sourcePhi_has_fixed_point q
  · exact sourcePhi_is_improper

/-- The first vertex is extreme in the three-action simplex. -/
lemma vertex0_extreme_simplex3 : extremePoint simplex3 vertex0 := by
  refine ⟨?_, ?_⟩
  · constructor
    · intro i
      fin_cases i <;> norm_num [vertex0]
    · rw [sum_fin3]
      norm_num [vertex0]
  intro y hy z hz a b ha hb hab hcomb
  have hcomb1 := congrFun hcomb 1
  have hcomb2 := congrFun hcomb 2
  norm_num [vertex0, Pi.smul_apply, Pi.add_apply] at hcomb1 hcomb2
  have hy1 : y 1 = 0 := by
    nlinarith [hy.1 1, hz.1 1]
  have hz1 : z 1 = 0 := by
    nlinarith [hy.1 1, hz.1 1]
  have hy2 : y 2 = 0 := by
    nlinarith [hy.1 2, hz.1 2]
  have hz2 : z 2 = 0 := by
    nlinarith [hy.1 2, hz.1 2]
  have hysum : y 0 + y 1 + y 2 = 1 := by
    rw [← sum_fin3]
    exact hy.2
  have hzsum : z 0 + z 1 + z 2 = 1 := by
    rw [← sum_fin3]
    exact hz.2
  have hy0 : y 0 = 1 := by linarith
  have hz0 : z 0 = 1 := by linarith
  constructor
  · ext i
    fin_cases i <;> simp [vertex0, hy0, hy1, hy2]
  · ext i
    fin_cases i <;> simp [vertex0, hz0, hz1, hz2]

/-- The source's two opposite endpoint comparators have antipodal nonzero
displacements at the first simplex vertex. -/
lemma sourceAB_antipodal_at_vertex0 :
    antipodalDisplacements sourceCoefficients sourcePhi vertex0 := by
  refine ⟨(1, 0), ?_, (-1, 0), ?_, 1, by norm_num, ?_, ?_⟩
  · norm_num [sourceCoefficients]
  · norm_num [sourceCoefficients]
  · refine ⟨0, ?_⟩
    norm_num [displacementFor, sourcePhi, sourceA, sourceB, vertex0,
      Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Matrix.of_apply,
      Matrix.cons_val', Matrix.head_cons, Matrix.tail_cons, Matrix.vecHead,
      Matrix.vecTail, Matrix.cons_val_one, Matrix.cons_val_two,
      Pi.smul_apply, Function.comp_apply]
  · ext i
    fin_cases i <;>
      norm_num [displacementFor, sourcePhi, sourceA, sourceB, vertex0,
        Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Matrix.of_apply,
        Matrix.cons_val', Matrix.head_cons, Matrix.tail_cons, Matrix.vecHead,
        Matrix.vecTail, Matrix.cons_val_one, Matrix.cons_val_two,
        Pi.smul_apply, Function.comp_apply]

/-- The all-ones vector is a common invariant for the source's second family.
This records why the affine-hyperplane obstruction alone does not rule this
family out. -/
theorem sourceAB_has_nonzero_common_invariant :
    ∃ v : Vec3, nonzeroVec3 v ∧
      commonInvariantOn simplex3 sourceCoefficients sourcePhi v := by
  refine ⟨(fun _ => (1 : ℝ)), ⟨0, by norm_num⟩, ?_⟩
  rw [commonInvariantOn]
  rintro ⟨a, b⟩ _ p _
  norm_num [displacementFor, sourcePhi, sourceA, sourceB, Matrix.mulVec,
    dotProduct, Fin.sum_univ_succ, Matrix.of_apply, Matrix.cons_val',
    Matrix.head_cons, Matrix.tail_cons, Matrix.vecHead, Matrix.vecTail,
    Matrix.cons_val_one, Matrix.cons_val_two, Pi.smul_apply,
    Function.comp_apply]
  ring

lemma vertex0_mem_simplex3 : vertex0 ∈ simplex3 := by
  constructor
  · intro i
    fin_cases i <;> norm_num [vertex0]
  · rw [sum_fin3]
    norm_num [vertex0]

lemma vertex1_mem_simplex3 : vertex1 ∈ simplex3 := by
  constructor
  · intro i
    fin_cases i <;> norm_num [vertex1]
  · rw [sum_fin3]
    norm_num [vertex1]

lemma vertex2_mem_simplex3 : vertex2 ∈ simplex3 := by
  constructor
  · intro i
    fin_cases i <;> norm_num [vertex2]
  · rw [sum_fin3]
    norm_num [vertex2]

lemma fixedPoint_mem_simplex3 (q : Vec3) (hq : q ∈ simplex3) :
    ![q 2, q 1, q 0] ∈ simplex3 := by
  constructor
  · intro i
    fin_cases i
    · simpa using hq.1 2
    · simpa using hq.1 1
    · simpa using hq.1 0
  · have hsum := hq.2
    norm_num [simplex3, Fin.sum_univ_succ] at hsum ⊢
    linarith

lemma skewPhi_fixedPoint (q : Vec3) :
    skewPhi q ![q 2, q 1, q 0] = ![q 2, q 1, q 0] := by
  ext i
  fin_cases i <;> simp [skewPhi] <;> ring

lemma corrected_column0_sum (S : Matrix (Fin 3) (Fin 3) ℝ)
    (h : corrected S vertex0 vertex1 ∈ simplex3) :
    S 0 0 + S 1 0 + S 2 0 = 0 := by
  have hdiff : skewPhi vertex0 vertex1 - vertex1 = -vertex0 := by
    ext i
    fin_cases i <;> norm_num [skewPhi, vertex0, vertex1]
  have hs := h.2
  rw [corrected, displacement, hdiff] at hs
  norm_num [Matrix.mulVec, dotProduct, vertex0, vertex1, Fin.sum_univ_succ] at hs ⊢
  linarith

lemma corrected_column1_sum (S : Matrix (Fin 3) (Fin 3) ℝ)
    (h : corrected S vertex0 vertex0 ∈ simplex3) :
    S 0 1 + S 1 1 + S 2 1 = 0 := by
  have hdiff : skewPhi vertex0 vertex0 - vertex0 = vertex1 := by
    ext i
    fin_cases i <;> norm_num [skewPhi, vertex0, vertex1]
  have hs := h.2
  rw [corrected, displacement, hdiff] at hs
  norm_num [Matrix.mulVec, dotProduct, vertex0, vertex1, Fin.sum_univ_succ] at hs ⊢
  linarith

lemma corrected_column2_sum (S : Matrix (Fin 3) (Fin 3) ℝ)
    (h : corrected S vertex1 vertex0 ∈ simplex3) :
    S 0 2 + S 1 2 + S 2 2 = 0 := by
  have hdiff : skewPhi vertex1 vertex0 - vertex0 = -vertex2 := by
    ext i
    fin_cases i <;> norm_num [skewPhi, vertex0, vertex1, vertex2]
  have hs := h.2
  rw [corrected, displacement, hdiff] at hs
  norm_num [Matrix.mulVec, dotProduct, vertex0, vertex2, Fin.sum_univ_succ] at hs ⊢
  linarith

lemma det_eq_zero_of_column_sums (S : Matrix (Fin 3) (Fin 3) ℝ)
    (h0 : S 0 0 + S 1 0 + S 2 0 = 0)
    (h1 : S 0 1 + S 1 1 + S 2 1 = 0)
    (h2 : S 0 2 + S 1 2 + S 2 2 = 0) : S.det = 0 := by
  have hs20 : S 2 0 = -S 0 0 - S 1 0 := by linarith
  have hs21 : S 2 1 = -S 0 1 - S 1 1 := by linarith
  have hs22 : S 2 2 = -S 0 2 - S 1 2 := by linarith
  rw [Matrix.det_fin_three]
  rw [hs20, hs21, hs22]
  ring

/-- The column-sum functional of a three-by-three matrix.  In the source's
invariant-vector argument this is the vector obtained by transporting the
simplex's affine defining functional through a candidate correction matrix. -/
def columnSums (S : Matrix (Fin 3) (Fin 3) ℝ) : Vec3 :=
  fun j => ∑ i, S i j

lemma sum_mulVec_eq_dot_columnSums (S : Matrix (Fin 3) (Fin 3) ℝ) (x : Vec3) :
    ∑ i, (S *ᵥ x) i = dotProduct (columnSums S) x := by
  simp only [Matrix.mulVec, dotProduct, columnSums]
  rw [Finset.sum_comm]
  simp_rw [Finset.sum_mul]

/-- The three-simplex has the all-ones affine hyperplane witness. -/
lemma simplex3_affineHyperplaneWitness : affineHyperplaneWitness simplex3 := by
  refine ⟨(fun _ => (1 : ℝ)), 1, ?_, ?_⟩
  · exact ⟨0, by norm_num⟩
  · intro p hp
    simpa [dotProduct] using hp.2

/-- An invertible canonical properizer on an action set contained in an
affine hyperplane transports that hyperplane normal to a nonzero common
invariant.  This is the dimension-three affine-hyperplane core of Lemma 4 in
D. Dann et al., *Rate-Preserving Reductions for Blackwell Approachability*,
COLT 2025.  The hypothesis is the source's canonical correction equation;
the separate derivation of that equation from general linear equivalence is
outside this development's stated scope. -/
theorem affine_hyperplane_canonical_properizer_has_nonzero_common_invariant
    {α : Type u} (P : Set Vec3) (Q : Set α) (φ : α → Vec3 → Vec3)
    (S : Matrix (Fin 3) (Fin 3) ℝ) (hdet : S.det ≠ 0)
    (haff : affineHyperplaneWitness P)
    (hproper : canonicalProperOn P Q φ S) :
    ∃ v : Vec3, nonzeroVec3 v ∧ commonInvariantOn P Q φ v := by
  obtain ⟨w, b, hw, hplane⟩ := haff
  let v : Vec3 := S.transpose *ᵥ w
  have hv : nonzeroVec3 v := by
    by_contra hnot
    rw [nonzeroVec3] at hnot
    have hvzero : v = 0 := by
      ext i
      by_contra hvi
      exact hnot ⟨i, hvi⟩
    have hdet_transpose : S.transpose.det ≠ 0 := by
      simpa using hdet
    have hwzero : w = 0 :=
      Matrix.eq_zero_of_mulVec_eq_zero hdet_transpose (by simpa [v] using hvzero)
    obtain ⟨i, hi⟩ := hw
    exact hi (by simp [hwzero])
  refine ⟨v, hv, ?_⟩
  rw [commonInvariantOn]
  intro q hq p hp
  have hcorrect_plane : dotProduct (correctedFor φ S q p) w = b :=
    hplane _ (hproper q hq p hp)
  have hp_plane : dotProduct p w = b := hplane p hp
  have hsum : dotProduct p w + dotProduct (S *ᵥ displacementFor φ q p) w = b := by
    calc
      dotProduct p w + dotProduct (S *ᵥ displacementFor φ q p) w =
          dotProduct (p + S *ᵥ displacementFor φ q p) w := by
            simp [dotProduct, Pi.add_apply, add_mul, Finset.sum_add_distrib]
      _ = b := by simpa [correctedFor] using hcorrect_plane
  have htransport : dotProduct (S *ᵥ displacementFor φ q p) w = 0 := by
    linarith [hsum, hp_plane]
  calc
    dotProduct (displacementFor φ q p) v =
        dotProduct w (S *ᵥ displacementFor φ q p) := by
          simpa [v] using Matrix.dotProduct_transpose_mulVec
            (A := S) (x := displacementFor φ q p) (y := w)
    _ = dotProduct (S *ᵥ displacementFor φ q p) w := dotProduct_comm _ _
    _ = 0 := htransport

/-- The canonical-correction core of Lemma 5 in Dann et al.: if two selected
comparators have nonzero antipodal displacements at an extreme action, no
invertible correction can map both back into the action set.  As with the
affine-hyperplane theorem above, this statement assumes the source's
canonical correction equation directly. -/
theorem extreme_antipodal_no_canonical_properizer
    {α : Type u} (P : Set Vec3) (Q : Set α) (φ : α → Vec3 → Vec3) (x : Vec3)
    (hx : extremePoint P x) (hanti : antipodalDisplacements Q φ x) :
    ∀ S : Matrix (Fin 3) (Fin 3) ℝ, S.det ≠ 0 → ¬ canonicalProperOn P Q φ S := by
  intro S hdet hproper
  obtain ⟨q₁, hq₁, q₂, hq₂, c, hc, hdnonzero, hdisplacement⟩ := hanti
  let d : Vec3 := displacementFor φ q₁ x
  let u : Vec3 := S *ᵥ d
  have hy : x + u ∈ P := by
    simpa [u, d, correctedFor] using hproper q₁ hq₁ x hx.1
  have hz : x - c • u ∈ P := by
    have hcorrect := hproper q₂ hq₂ x hx.1
    rw [correctedFor] at hcorrect
    rw [hdisplacement] at hcorrect
    have hmul : S *ᵥ -(c • displacementFor φ q₁ x) =
        -(c • S *ᵥ displacementFor φ q₁ x) := by
      rw [Matrix.mulVec_neg, Matrix.mulVec_smul]
    rw [hmul] at hcorrect
    simpa [u, d, sub_eq_add_neg] using hcorrect
  let a : ℝ := c / (1 + c)
  let b : ℝ := 1 / (1 + c)
  have hden : 0 < 1 + c := by linarith
  have ha : 0 < a := by
    exact div_pos hc hden
  have hb : 0 < b := by
    exact one_div_pos.mpr hden
  have hab : a + b = 1 := by
    dsimp [a, b]
    field_simp [ne_of_gt hden]
    ring
  have hcomb : x = a • (x + u) + b • (x - c • u) := by
    ext i
    dsimp [a, b]
    simp
    field_simp [ne_of_gt hden]
    ring
  have hyx : x + u = x :=
    (hx.2 (x + u) hy (x - c • u) hz a b ha hb hab hcomb).1
  have hu : u = 0 := by
    apply add_left_cancel (a := x)
    simpa using hyx
  have hdzero : d = 0 :=
    Matrix.eq_zero_of_mulVec_eq_zero hdet (by simpa [u] using hu)
  rw [nonzeroVec3] at hdnonzero
  obtain ⟨i, hi⟩ := hdnonzero
  exact hi (by simpa [d] using congrFun hdzero i)

/-- The second explicit source family cannot have an invertible canonical
properizer.  This instantiates the canonical-correction core of Lemma 5 with
the verified fixed-point family and its antipodal vertex displacements. -/
theorem sourceAB_not_canonically_proper_reducible :
    ¬ ∃ S : Matrix (Fin 3) (Fin 3) ℝ,
      S.det ≠ 0 ∧ canonicalProperOn simplex3 sourceCoefficients sourcePhi S := by
  rintro ⟨S, hdet, hproper⟩
  exact
    extreme_antipodal_no_canonical_properizer simplex3 sourceCoefficients
      sourcePhi vertex0 vertex0_extreme_simplex3 sourceAB_antipodal_at_vertex0
      S hdet hproper

/-- Every invertible canonical properizer of a three-action comparator family
transports the simplex sum functional to a nonzero common invariant.  This is
the reusable finite-dimensional lemma behind the source's first
irreducibility obstruction. -/
theorem canonical_properizer_has_nonzero_common_invariant
    {α : Type u} (Q : Set α) (φ : α → Vec3 → Vec3)
    (S : Matrix (Fin 3) (Fin 3) ℝ) (hdet : S.det ≠ 0)
    (hproper : canonicalProperFor Q φ S) :
    ∃ v : Vec3, nonzeroVec3 v ∧ commonInvariantFor Q φ v := by
  let v : Vec3 := columnSums S
  have hv : nonzeroVec3 v := by
    by_contra hnot
    rw [nonzeroVec3] at hnot
    have hvzero : ∀ i, v i = 0 := by
      intro i
      by_contra hzero
      exact hnot ⟨i, hzero⟩
    apply hdet
    apply det_eq_zero_of_column_sums S
    · simpa [v, columnSums, Fin.sum_univ_succ, add_assoc] using hvzero 0
    · simpa [v, columnSums, Fin.sum_univ_succ, add_assoc] using hvzero 1
    · simpa [v, columnSums, Fin.sum_univ_succ, add_assoc] using hvzero 2
  refine ⟨v, hv, ?_⟩
  rw [commonInvariantFor]
  intro q hq p hp
  have hsum : ∑ i, (S *ᵥ displacementFor φ q p) i = 0 := by
    have hcorrect := (hproper q hq p hp).2
    have hcorrect' : (∑ i, p i) + ∑ i, (S *ᵥ displacementFor φ q p) i = 1 := by
      simpa [correctedFor, Pi.add_apply, Finset.sum_add_distrib]
        using hcorrect
    linarith [hcorrect', hp.2]
  rw [sum_mulVec_eq_dot_columnSums] at hsum
  simpa [v, dotProduct, mul_comm] using hsum

/-- A proper canonical correction transports the simplex's sum functional to
a nonzero common invariant of the original comparator family.  This is the
finite-dimensional mechanism behind the first irreducibility obstruction in
Dann et al., Section 4.4.1. -/
theorem canonical_proper_has_nonzero_common_invariant
    (S : Matrix (Fin 3) (Fin 3) ℝ) (hdet : S.det ≠ 0)
    (hproper : canonicalProper S) :
    ∃ v : Vec3, nonzeroVec3 v ∧ commonInvariant v := by
  simpa [canonicalProperFor, commonInvariantFor, correctedFor, displacementFor,
    canonicalProper, commonInvariant, corrected, displacement]
    using canonical_properizer_has_nonzero_common_invariant simplex3 skewPhi S hdet hproper

/-- The three skew comparators have no nonzero vector that is invariant for
every comparator.  Three explicit vertex tests force all coordinates of such
a vector to vanish. -/
theorem skewPhi_has_no_nonzero_common_invariant :
    ¬ ∃ v : Vec3, nonzeroVec3 v ∧ commonInvariant v := by
  rintro ⟨v, hv, hinvariant⟩
  rw [commonInvariant] at hinvariant
  have h0 := hinvariant vertex0 vertex0_mem_simplex3
    vertex1 vertex1_mem_simplex3
  have h1 := hinvariant vertex0 vertex0_mem_simplex3
    vertex0 vertex0_mem_simplex3
  have h2 := hinvariant vertex1 vertex1_mem_simplex3
    vertex0 vertex0_mem_simplex3
  norm_num [displacement, skewPhi, vertex0, vertex1, vertex2, dotProduct,
    Fin.sum_univ_succ] at h0 h1 h2
  rw [nonzeroVec3] at hv
  obtain ⟨i, hi⟩ := hv
  fin_cases i
  · exact hi (by simpa using h0)
  · exact hi (by simpa using h1)
  · exact hi (by simpa using h2)

lemma skewPhi_fixed_point_in_simplex (q : Vec3) (hq : q ∈ simplex3) :
    ∃ p ∈ simplex3, skewPhi q p = p := by
  refine ⟨![q 2, q 1, q 0], fixedPoint_mem_simplex3 q hq, ?_⟩
  exact skewPhi_fixedPoint q

lemma skewPhi_is_improper :
    ∃ q ∈ simplex3, ∃ p ∈ simplex3, skewPhi q p ∉ simplex3 := by
  refine ⟨vertex0, vertex0_mem_simplex3, vertex1, vertex1_mem_simplex3, ?_⟩
  intro h
  have hnonneg := h.1 0
  norm_num [skewPhi, vertex0, vertex1] at hnonneg

/-- The three skew comparators form a valid improper phi-regret family: every
convexly mixed comparator has a fixed point, while one explicit comparator is
not simplex-preserving. -/
theorem skewPhi_valid_improper_instance : validImproperInstance := by
  constructor
  · intro q hq
    exact skewPhi_fixed_point_in_simplex q hq
  · exact skewPhi_is_improper

/-- Any matrix that makes every corrected comparator simplex-preserving has
zero determinant.  The three vertex tests force its three column sums to
vanish, and hence make the rows linearly dependent. -/
theorem canonical_proper_matrices_are_singular (S : Matrix (Fin 3) (Fin 3) ℝ)
    (hproper : canonicalProper S) : S.det = 0 := by
  apply det_eq_zero_of_column_sums S
  · exact corrected_column0_sum S
      (hproper vertex0 vertex0_mem_simplex3 vertex1 vertex1_mem_simplex3)
  · exact corrected_column1_sum S
      (hproper vertex0 vertex0_mem_simplex3 vertex0 vertex0_mem_simplex3)
  · exact corrected_column2_sum S
      (hproper vertex1 vertex1_mem_simplex3 vertex0 vertex0_mem_simplex3)

/-- The explicit improper family admits no invertible canonical correction
that turns all its comparators into proper simplex self-maps. -/
theorem skewPhi_not_canonically_proper_reducible : ¬ canonicalProperReduction := by
  rintro ⟨S, hdet, hproper⟩
  obtain ⟨v, hv, hinvariant⟩ :=
    affine_hyperplane_canonical_properizer_has_nonzero_common_invariant
      simplex3 simplex3 skewPhi S hdet simplex3_affineHyperplaneWitness
      (by
        simpa [canonicalProperOn, canonicalProper, correctedFor, corrected,
          displacementFor, displacement] using hproper)
  apply skewPhi_has_no_nonzero_common_invariant
  refine ⟨v, hv, ?_⟩
  simpa [commonInvariantOn, commonInvariant, displacementFor, displacement]
    using hinvariant

end Blackwell.Irreducibility
