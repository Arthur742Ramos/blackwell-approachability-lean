import Mathlib.Data.Real.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option autoImplicit false

open scoped BigOperators

namespace Blackwell.NonnegativeRank.Palomar

universe u v

def IsProbabilityMatrix {m : Type u} {n : Type v}
    [Fintype m] [Fintype n] (P : m → n → ℝ) : Prop :=
  (∀ i j, 0 ≤ P i j) ∧ (∑ i, ∑ j, P i j) = 1

def HasNonnegativeFactorization {m : Type u} {n : Type v}
    [Fintype m] [Fintype n] (P : m → n → ℝ) (k : ℕ) : Prop :=
  ∃ U : m → Fin k → ℝ, ∃ V : Fin k → n → ℝ,
    (∀ i r, 0 ≤ U i r) ∧
    (∀ r j, 0 ≤ V r j) ∧
    (∀ i j, P i j = ∑ r, U i r * V r j)

def HasProductMixture {m : Type u} {n : Type v}
    [Fintype m] [Fintype n] (P : m → n → ℝ) (k : ℕ) : Prop :=
  ∃ w : Fin k → ℝ, ∃ p : Fin k → m → ℝ, ∃ q : Fin k → n → ℝ,
    (∀ r, 0 ≤ w r) ∧
    (∑ r, w r) = 1 ∧
    (∀ r i, 0 ≤ p r i) ∧
    (∀ r, ∑ i, p r i = 1) ∧
    (∀ r j, 0 ≤ q r j) ∧
    (∀ r, ∑ j, q r j = 1) ∧
    (∀ i j, P i j = ∑ r, w r * p r i * q r j)

def IsLeastNonnegativeFactorizationCount {m : Type u} {n : Type v}
    [Fintype m] [Fintype n] (P : m → n → ℝ) (k : ℕ) : Prop :=
  HasNonnegativeFactorization P k ∧
    ∀ ℓ, HasNonnegativeFactorization P ℓ → k ≤ ℓ

def IsLeastProductMixtureCount {m : Type u} {n : Type v}
    [Fintype m] [Fintype n] (P : m → n → ℝ) (k : ℕ) : Prop :=
  HasProductMixture P k ∧ ∀ ℓ, HasProductMixture P ℓ → k ≤ ℓ

def IsFoolingSet {m : Type u} {n : Type v}
    [Fintype m] [Fintype n] (P : m → n → ℝ) (ℓ : ℕ)
    (f : Fin ℓ → m × n) : Prop :=
  Function.Injective f ∧
    (∀ s, 0 < P (f s).1 (f s).2) ∧
    (∀ s t, s ≠ t →
      P (f s).1 (f t).2 = 0 ∨ P (f t).1 (f s).2 = 0)

noncomputable def uniformDiagonal (N : ℕ) (i j : Fin N) : ℝ :=
  if i = j then (N : ℝ)⁻¹ else 0

theorem productMixture_iff_nonnegativeFactorization
    {m : Type u} {n : Type v} [Fintype m] [Fintype n]
    [Nonempty m] [Nonempty n] (P : m → n → ℝ)
    (hP : IsProbabilityMatrix P) (k : ℕ) :
    HasProductMixture P k ↔ HasNonnegativeFactorization P k := by
  classical
  constructor
  · rintro ⟨w, p, q, hw, hw_sum, hp, hp_sum, hq, hq_sum, hmix⟩
    refine ⟨fun i r => w r * p r i, q, ?_, hq, ?_⟩
    · intro i r
      exact mul_nonneg (hw r) (hp r i)
    · intro i j
      exact hmix i j
  · rintro ⟨U, V, hU, hV, hfactor⟩
    let a : Fin k → ℝ := fun r => ∑ i, U i r
    let b : Fin k → ℝ := fun r => ∑ j, V r j
    let w : Fin k → ℝ := fun r => a r * b r
    let p : Fin k → m → ℝ := fun r i =>
      if a r = 0 then
        if i = Classical.choice (inferInstanceAs (Nonempty m)) then 1 else 0
      else U i r / a r
    let q : Fin k → n → ℝ := fun r j =>
      if b r = 0 then
        if j = Classical.choice (inferInstanceAs (Nonempty n)) then 1 else 0
      else V r j / b r
    have ha_nonneg (r : Fin k) : 0 ≤ a r := by
      exact Finset.sum_nonneg fun i hi => hU i r
    have hb_nonneg (r : Fin k) : 0 ≤ b r := by
      exact Finset.sum_nonneg fun j hj => hV r j
    have ha_pos (r : Fin k) (hz : a r ≠ 0) : 0 < a r := by
      rcases lt_or_eq_of_le (ha_nonneg r) with hlt | heq
      · exact hlt
      · exact (hz heq.symm).elim
    have hb_pos (r : Fin k) (hz : b r ≠ 0) : 0 < b r := by
      rcases lt_or_eq_of_le (hb_nonneg r) with hlt | heq
      · exact hlt
      · exact (hz heq.symm).elim
    have hU_zero (r : Fin k) (hz : a r = 0) (i : m) : U i r = 0 := by
      have hle : U i r ≤ ∑ i', U i' r :=
        Finset.single_le_sum (fun i' hi' => hU i' r) (Finset.mem_univ i)
      have : U i r ≤ 0 := by simpa [a, hz] using hle
      exact le_antisymm this (hU i r)
    have hV_zero (r : Fin k) (hz : b r = 0) (j : n) : V r j = 0 := by
      have hle : V r j ≤ ∑ j', V r j' :=
        Finset.single_le_sum (fun j' hj' => hV r j') (Finset.mem_univ j)
      have : V r j ≤ 0 := by simpa [b, hz] using hle
      exact le_antisymm this (hV r j)
    have hw_nonneg : ∀ r, 0 ≤ w r := by
      intro r
      exact mul_nonneg (ha_nonneg r) (hb_nonneg r)
    have hp_nonneg : ∀ r i, 0 ≤ p r i := by
      intro r i
      by_cases hz : a r = 0
      · simp only [p, if_pos hz]
        split_ifs <;> norm_num
      · simpa [p, hz] using div_nonneg (hU i r) (le_of_lt (ha_pos r hz))
    have hp_sum : ∀ r, ∑ i, p r i = 1 := by
      intro r
      by_cases hz : a r = 0
      · simp [p, hz]
      · have hden : 0 < a r := ha_pos r hz
        calc
          ∑ i, p r i = (∑ i, U i r) / a r := by
            simp [p, hz, Finset.sum_div]
          _ = 1 := by simp [a, div_self hden.ne']
    have hq_nonneg : ∀ r j, 0 ≤ q r j := by
      intro r j
      by_cases hz : b r = 0
      · simp only [q, if_pos hz]
        split_ifs <;> norm_num
      · simpa [q, hz] using div_nonneg (hV r j) (le_of_lt (hb_pos r hz))
    have hq_sum : ∀ r, ∑ j, q r j = 1 := by
      intro r
      by_cases hz : b r = 0
      · simp [q, hz]
      · have hden : 0 < b r := hb_pos r hz
        calc
          ∑ j, q r j = (∑ j, V r j) / b r := by
            simp [q, hz, Finset.sum_div]
          _ = 1 := by simp [b, div_self hden.ne']
    have htotal_factorization :
        (∑ i, ∑ j, P i j) = ∑ r, a r * b r := by
      calc
        (∑ i, ∑ j, P i j) = ∑ i, ∑ j, ∑ r, U i r * V r j := by
          simp_rw [hfactor]
        _ = ∑ i, ∑ r, ∑ j, U i r * V r j := by
          congr 1
          funext i
          exact Finset.sum_comm
        _ = ∑ r, ∑ i, ∑ j, U i r * V r j := by
          exact Finset.sum_comm
        _ = ∑ r, (∑ i, U i r) * (∑ j, V r j) := by
          apply Finset.sum_congr rfl
          intro r hr
          rw [Fintype.sum_mul_sum]
        _ = ∑ r, a r * b r := by simp [a, b]
    have hw_sum : ∑ r, w r = 1 := by
      calc
        ∑ r, w r = ∑ r, a r * b r := by rfl
        _ = ∑ i, ∑ j, P i j := htotal_factorization.symm
        _ = 1 := hP.2
    have hmix : ∀ i j, P i j = ∑ r, w r * p r i * q r j := by
      intro i j
      rw [hfactor i j]
      apply Finset.sum_congr rfl
      intro r hr
      by_cases ha : a r = 0
      · simp [w, p, q, ha, hU_zero r ha i]
      · by_cases hb : b r = 0
        · simp [w, p, q, hb, hV_zero r hb j]
        · simp [w, p, q, ha, hb]
          field_simp
    exact ⟨w, p, q, hw_nonneg, hw_sum, hp_nonneg, hp_sum,
      hq_nonneg, hq_sum, hmix⟩

theorem leastProductMixtureCount_iff_leastNonnegativeFactorizationCount
    {m : Type u} {n : Type v} [Fintype m] [Fintype n]
    [Nonempty m] [Nonempty n] (P : m → n → ℝ)
    (hP : IsProbabilityMatrix P) (k : ℕ) :
    IsLeastProductMixtureCount P k ↔ IsLeastNonnegativeFactorizationCount P k := by
  constructor
  · rintro ⟨hmix, hleast⟩
    refine ⟨(productMixture_iff_nonnegativeFactorization P hP k).1 hmix, ?_⟩
    intro ℓ hfactor
    exact hleast ℓ ((productMixture_iff_nonnegativeFactorization P hP ℓ).2 hfactor)
  · rintro ⟨hfactor, hleast⟩
    refine ⟨(productMixture_iff_nonnegativeFactorization P hP k).2 hfactor, ?_⟩
    intro ℓ hmix
    exact hleast ℓ ((productMixture_iff_nonnegativeFactorization P hP ℓ).1 hmix)

private theorem exists_pos_term_of_pos_sum {k : ℕ} (f : Fin k → ℝ)
    (hnonneg : ∀ r, 0 ≤ f r) (hsum : 0 < ∑ r, f r) : ∃ r, 0 < f r := by
  classical
  by_contra hnone
  have hzero : ∀ r, f r = 0 := by
    intro r
    apply le_antisymm
    · exact le_of_not_gt (fun hpos => hnone ⟨r, hpos⟩)
    · exact hnonneg r
  have hsum_zero : (∑ r, f r) = 0 := Finset.sum_eq_zero fun r hr => hzero r
  rw [hsum_zero] at hsum
  norm_num at hsum

theorem foolingSet_card_le_factorCount
    {m : Type u} {n : Type v} [Fintype m] [Fintype n]
    {P : m → n → ℝ} {ℓ k : ℕ} {f : Fin ℓ → m × n}
    (hF : IsFoolingSet P ℓ f)
    (hfactor : HasNonnegativeFactorization P k) : ℓ ≤ k := by
  classical
  rcases hfactor with ⟨U, V, hU, hV, hfactor⟩
  have hcomponent : ∀ s, ∃ r, 0 < U (f s).1 r ∧ 0 < V r (f s).2 := by
    intro s
    have hsum : 0 < ∑ r, U (f s).1 r * V r (f s).2 := by
      rw [← hfactor]
      exact hF.2.1 s
    obtain ⟨r, hr⟩ := exists_pos_term_of_pos_sum
      (fun r => U (f s).1 r * V r (f s).2)
      (fun r => mul_nonneg (hU _ _) (hV _ _)) hsum
    refine ⟨r, ?_, ?_⟩
    · by_contra hnot
      have hle : U (f s).1 r ≤ 0 := le_of_not_gt hnot
      nlinarith [hU (f s).1 r, hV r (f s).2, hr]
    · by_contra hnot
      have hle : V r (f s).2 ≤ 0 := le_of_not_gt hnot
      nlinarith [hU (f s).1 r, hV r (f s).2, hr]
  let component : Fin ℓ → Fin k := fun s => Classical.choose (hcomponent s)
  have hcomponent_spec (s : Fin ℓ) :
      0 < U (f s).1 (component s) ∧ 0 < V (component s) (f s).2 :=
    Classical.choose_spec (hcomponent s)
  have hentry_pos {i : m} {j : n} {r : Fin k}
      (hu : 0 < U i r) (hv : 0 < V r j) : 0 < P i j := by
    rw [hfactor i j]
    exact lt_of_lt_of_le (mul_pos hu hv)
      (Finset.single_le_sum (fun r' hr' => mul_nonneg (hU i r') (hV r' j))
        (Finset.mem_univ r))
  have hinj : Function.Injective component := by
    intro s t hst
    by_contra hne
    rcases hF.2.2 s t hne with hzero | hzero
    · have hVt := (hcomponent_spec t).2
      rw [← hst] at hVt
      have hpos := hentry_pos (hcomponent_spec s).1 hVt
      rw [hzero] at hpos
      norm_num at hpos
    · have hUt := (hcomponent_spec t).1
      rw [← hst] at hUt
      have hpos := hentry_pos hUt (hcomponent_spec s).2
      rw [hzero] at hpos
      norm_num at hpos
  simpa using Fintype.card_le_of_injective component hinj

theorem uniformDiagonal_has_productMixture
    {N : ℕ} (hN : 0 < N) :
    HasProductMixture (uniformDiagonal N) N := by
  letI : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  have hP : IsProbabilityMatrix (uniformDiagonal N) := by
    have hNreal : 0 < (N : ℝ) := by exact_mod_cast hN
    constructor
    · intro i j
      by_cases hij : i = j
      · simp [uniformDiagonal, hij, inv_nonneg.mpr (le_of_lt hNreal)]
      · simp [uniformDiagonal, hij]
    · have hrow : ∀ i : Fin N, ∑ j, uniformDiagonal N i j = (N : ℝ)⁻¹ := by
        intro i
        simp [uniformDiagonal]
      calc
        (∑ i, ∑ j, uniformDiagonal N i j) = ∑ i, (N : ℝ)⁻¹ := by
          apply Finset.sum_congr rfl
          intro i hi
          exact hrow i
        _ = (N : ℝ) * (N : ℝ)⁻¹ := by simp [Fintype.card_fin]
        _ = 1 := by field_simp
  have hfactor : HasNonnegativeFactorization (uniformDiagonal N) N := by
    refine ⟨fun i r => if i = r then (N : ℝ)⁻¹ else 0,
      fun r j => if r = j then 1 else 0, ?_, ?_, ?_⟩
    · intro i r
      by_cases hir : i = r
      · simp [hir, inv_nonneg.mpr (show 0 ≤ (N : ℝ) from le_of_lt (by exact_mod_cast hN))]
      · simp [hir]
    · intro r j
      by_cases hrj : r = j <;> simp [hrj]
    · intro i j
      by_cases hij : i = j
      · subst j
        simp [uniformDiagonal, eq_comm]
      · simp [uniformDiagonal, hij, eq_comm]
  exact (productMixture_iff_nonnegativeFactorization
    (uniformDiagonal N) hP N).2 hfactor

theorem uniformDiagonal_mixture_minimal
    {N k : ℕ} (hN : 0 < N)
    (hmixture : HasProductMixture (uniformDiagonal N) k) : N ≤ k := by
  letI : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  have hNreal : 0 < (N : ℝ) := by exact_mod_cast hN
  have hP : IsProbabilityMatrix (uniformDiagonal N) := by
    constructor
    · intro i j
      by_cases hij : i = j
      · simp [uniformDiagonal, hij, inv_nonneg.mpr (le_of_lt hNreal)]
      · simp [uniformDiagonal, hij]
    · have hrow : ∀ i : Fin N, ∑ j, uniformDiagonal N i j = (N : ℝ)⁻¹ := by
        intro i
        simp [uniformDiagonal]
      calc
        (∑ i, ∑ j, uniformDiagonal N i j) = ∑ i, (N : ℝ)⁻¹ := by
          apply Finset.sum_congr rfl
          intro i hi
          exact hrow i
        _ = (N : ℝ) * (N : ℝ)⁻¹ := by simp [Fintype.card_fin]
        _ = 1 := by field_simp
  have hfactor := (productMixture_iff_nonnegativeFactorization
    (uniformDiagonal N) hP k).mp hmixture
  let f : Fin N → Fin N × Fin N := fun i => (i, i)
  have hF : IsFoolingSet (uniformDiagonal N) N f := by
    constructor
    · intro i j hij
      exact congrArg Prod.fst hij
    constructor
    · intro i
      simp [f, uniformDiagonal, hNreal]
    · intro i j hij
      left
      simp [f, uniformDiagonal, hij]
  exact foolingSet_card_le_factorCount hF hfactor

end Blackwell.NonnegativeRank.Palomar
