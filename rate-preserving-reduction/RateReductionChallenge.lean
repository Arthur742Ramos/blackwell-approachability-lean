import Mathlib

set_option autoImplicit false

/-!
# Challenge: finite tight approachability-to-improper-regret reduction

This Mathlib-only statement surface isolates a finite-simplex version of
Theorem 4 from Dann, Mansour, Mohri, Schneider, and Sivan (COLT 2025).
The constraint set is a finite convex hull, the original action set is a
finite simplex, and `JointMixed m n` is the convex hull of the elementary
tensors.  The action marginal is the canonical decoder.

The selected claims prove that the lift and decoder stay in their action
sets, that the comparator `shift w x = x + w tensor marginal(x)` is improper,
and that its regret equals the original approachability loss exactly at every
finite horizon in both translation directions.  This is a finite
convex-hull realization of the source construction; it makes no claim about
the source's general infinite-dimensional or randomized framework.
-/

namespace Blackwell.RateReduction.Palomar

open scoped BigOperators

noncomputable section

abbrev Dist (n : Type) := n → ℝ
abbrev Joint (m n : Type) := m → n → ℝ

def simplex {n : Type} [Fintype n] (p : Dist n) : Prop :=
  (∀ i, 0 ≤ p i) ∧ (∑ i, p i) = 1

abbrev Mixed (n : Type) [Fintype n] := {p : Dist n // simplex p}

def jointSimplex {m n : Type} [Fintype m] [Fintype n]
    (x : Joint m n) : Prop :=
  (∀ i j, 0 ≤ x i j) ∧ (∑ i, ∑ j, x i j) = 1

abbrev JointMixed (m n : Type) [Fintype m] [Fintype n] :=
  {x : Joint m n // jointSimplex x}

def marginal {m n : Type} [Fintype m] (x : Joint m n) : Dist n :=
  fun j => ∑ i, x i j

def outer {m n : Type} (w : Dist m) (p : Dist n) : Joint m n :=
  fun i j => w i * p j

def shift {m n : Type} [Fintype m] (w : Dist m) (x : Joint m n) : Joint m n :=
  fun i j => x i j + outer w (marginal x) i j

/-- Marginalization maps the joint simplex back to the original action simplex. -/
theorem marginal_simplex {m n : Type} [Fintype m] [Fintype n]
    {x : Joint m n} (hx : jointSimplex x) : simplex (marginal x) := by
  sorry

/-- Elementary tensors of mixed constraints and actions are joint actions. -/
theorem outer_jointSimplex {m n : Type} [Fintype m] [Fintype n]
    {w : Dist m} {p : Dist n} (hw : simplex w) (hp : simplex p) :
    jointSimplex (outer w p) := by
  sorry

/-- Marginalization is a left inverse of the anchored tensor lift. -/
theorem marginal_outer {m n : Type} [Fintype m] [Fintype n]
    {w : Dist m} {p : Dist n} (hw : simplex w) :
    marginal (outer w p) = p := by
  sorry

def lift {m n : Type} [Fintype m] [Fintype n]
    (anchor : Mixed m) (p : Mixed n) : JointMixed m n :=
  ⟨outer anchor.1 p.1, outer_jointSimplex anchor.2 p.2⟩

def decode {m n : Type} [Fintype m] [Fintype n]
    (x : JointMixed m n) : Mixed n :=
  ⟨marginal x.1, marginal_simplex x.2⟩

lemma decode_lift {m n : Type} [Fintype m] [Fintype n]
    (anchor : Mixed m) (p : Mixed n) : decode (lift anchor p) = p := by
  apply Subtype.ext
  exact marginal_outer anchor.2

abbrev Payoff (m n d : Type) := m → n → d → ℝ

def reducedLoss {m n d : Type} [Fintype d]
    (u : Payoff m n d) (l : Dist d) : Joint m n :=
  fun i j => -(∑ k, u i j k * l k)

def flatten {m n : Type} (x : Joint m n) : m × n → ℝ :=
  fun ij => x ij.1 ij.2

def pairing {m n : Type} [Fintype m] [Fintype n]
    (x y : Joint m n) : ℝ :=
  dotProduct (flatten x) (flatten y)

def score {m n d : Type} [Fintype m] [Fintype n] [Fintype d]
    (u : Payoff m n d) (w : Dist m) (p : Dist n) (l : Dist d) : ℝ :=
  pairing (outer w p) (-reducedLoss u l)

/-- The exact source-style one-step equality. -/
theorem pairing_shift_sub_pairing_eq_score
    {m n d : Type} [Fintype m] [Fintype n] [Fintype d]
    (u : Payoff m n d) (w : Dist m) (x : Joint m n) (l : Dist d) :
    pairing x (reducedLoss u l) - pairing (shift w x) (reducedLoss u l) =
      score u w (marginal x) l := by
  sorry

def approachSum {m n d : Type} [Fintype m] [Fintype n] [Fintype d]
    {T : ℕ} (u : Payoff m n d) (w : Mixed m)
    (p : Fin T → Mixed n) (l : Fin T → Dist d) : ℝ :=
  ∑ t, score u w.1 (p t).1 (l t)

def regretSum {m n d : Type} [Fintype m] [Fintype n] [Fintype d]
    {T : ℕ} (u : Payoff m n d) (w : Mixed m)
    (x : Fin T → JointMixed m n) (l : Fin T → Dist d) : ℝ :=
  ∑ t, (pairing (x t).1 (reducedLoss u (l t)) -
    pairing (shift w.1 (x t).1) (reducedLoss u (l t)))

/-- Summing the pointwise identity preserves every finite-horizon objective. -/
theorem regretSum_eq_approachSum {m n d : Type} [Fintype m] [Fintype n] [Fintype d]
    {T : ℕ} (u : Payoff m n d) (w : Mixed m)
    (x : Fin T → JointMixed m n) (l : Fin T → Dist d) :
    regretSum u w x l = approachSum u w (fun t => decode (x t)) l := by
  sorry

def approachLoss {m n d : Type} [Fintype m] [Fintype n] [Fintype d]
    {T : ℕ} (u : Payoff m n d) (p : Fin T → Mixed n)
    (l : Fin T → Dist d) : ℝ :=
  sSup (Set.range fun w : Mixed m => approachSum u w p l)

def regretLoss {m n d : Type} [Fintype m] [Fintype n] [Fintype d]
    {T : ℕ} (u : Payoff m n d) (x : Fin T → JointMixed m n)
    (l : Fin T → Dist d) : ℝ :=
  sSup (Set.range fun w : Mixed m => regretSum u w x l)

def liftTrajectory {m n : Type} [Fintype m] [Fintype n]
    (anchor : Mixed m) {T : ℕ} (p : Fin T → Mixed n) : Fin T → JointMixed m n :=
  fun t => lift anchor (p t)

def decodeTrajectory {m n : Type} [Fintype m] [Fintype n]
    {T : ℕ} (x : Fin T → JointMixed m n) : Fin T → Mixed n :=
  fun t => decode (x t)

/-- Exact loss equality for every transformed joint trajectory. -/
theorem regretLoss_eq_approachLoss {m n d : Type} [Fintype m] [Fintype n] [Fintype d]
    {T : ℕ} (u : Payoff m n d) (x : Fin T → JointMixed m n)
    (l : Fin T → Dist d) :
    regretLoss u x l = approachLoss u (decodeTrajectory x) l := by
  sorry

theorem approach_to_regret_exact {m n d : Type} [Fintype m] [Fintype n] [Fintype d]
    {T : ℕ} (u : Payoff m n d) (anchor : Mixed m)
    (p : Fin T → Mixed n) (l : Fin T → Dist d) :
    regretLoss u (liftTrajectory anchor p) l = approachLoss u p l := by
  rw [regretLoss_eq_approachLoss]
  congr 1
  funext t
  exact decode_lift anchor (p t)

theorem regret_to_approach_exact {m n d : Type} [Fintype m] [Fintype n] [Fintype d]
    {T : ℕ} (u : Payoff m n d) (x : Fin T → JointMixed m n)
    (l : Fin T → Dist d) :
    approachLoss u (decodeTrajectory x) l = regretLoss u x l :=
  (regretLoss_eq_approachLoss u x l).symm

def FiniteTensorTightReduction {m n d : Type} [Fintype m] [Fintype n] [Fintype d]
    (u : Payoff m n d) (anchor : Mixed m) : Prop :=
  (∀ {T : ℕ} (p : Fin T → Mixed n) (l : Fin T → Dist d),
    regretLoss u (liftTrajectory anchor p) l = approachLoss u p l) ∧
  ∀ {T : ℕ} (x : Fin T → JointMixed m n) (l : Fin T → Dist d),
    approachLoss u (decodeTrajectory x) l = regretLoss u x l

/-- The comparator always escapes the joint-simplex action set. -/
def shiftImproper {m n : Type} [Fintype m] [Fintype n] : Prop :=
  ∀ w : Mixed m, ∀ x : JointMixed m n, ¬ jointSimplex (shift w.1 x.1)

theorem shift_is_improper {m n : Type} [Fintype m] [Fintype n] :
    shiftImproper (m := m) (n := n) := by
  sorry

/-- Both explicit translations preserve loss exactly at every finite horizon for
the supplied anchor. -/
theorem finiteTensorTightReduction_of_anchor
    {m n d : Type} [Fintype m] [Fintype n] [Fintype d]
    (u : Payoff m n d) (anchor : Mixed m) : FiniteTensorTightReduction u anchor := by
  sorry

/-- A deterministic online strategy receives exactly its prior loss history. -/
abbrev OnlineStrategy (A L : Type) := List L → A

def runTrajectory {A L : Type} (alg : OnlineStrategy A L)
    (losses : List L) : Fin losses.length → A :=
  fun t => alg (losses.take t.1)

def lossTrajectory {L : Type} (losses : List L) : Fin losses.length → L :=
  fun t => losses.get t

def liftStrategy {m n d : Type} [Fintype m] [Fintype n]
    (anchor : Mixed m) (alg : OnlineStrategy (Mixed n) (Dist d)) :
    OnlineStrategy (JointMixed m n) (Dist d) :=
  fun history => lift anchor (alg history)

def decodeStrategy {m n d : Type} [Fintype m] [Fintype n]
    (alg : OnlineStrategy (JointMixed m n) (Dist d)) :
    OnlineStrategy (Mixed n) (Dist d) :=
  fun history => decode (alg history)

def onlineApproachLoss {m n d : Type} [Fintype m] [Fintype n] [Fintype d]
    (u : Payoff m n d) (alg : OnlineStrategy (Mixed n) (Dist d))
    (losses : List (Dist d)) : ℝ :=
  approachLoss u (runTrajectory alg losses) (lossTrajectory losses)

def onlineRegretLoss {m n d : Type} [Fintype m] [Fintype n] [Fintype d]
    (u : Payoff m n d) (alg : OnlineStrategy (JointMixed m n) (Dist d))
    (losses : List (Dist d)) : ℝ :=
  regretLoss u (runTrajectory alg losses) (lossTrajectory losses)

/-- Tightness at the level of causal online strategies for the supplied anchor. -/
def AlgorithmicFiniteTensorTightReduction {m n d : Type}
    [Fintype m] [Fintype n] [Fintype d] (u : Payoff m n d)
    (anchor : Mixed m) : Prop :=
  (∀ alg losses,
    onlineRegretLoss u (liftStrategy anchor alg) losses = onlineApproachLoss u alg losses) ∧
  ∀ alg losses,
    onlineApproachLoss u (decodeStrategy alg) losses = onlineRegretLoss u alg losses

theorem algorithmicFiniteTensorTightReduction_of_anchor {m n d : Type}
    [Fintype m] [Fintype n] [Fintype d]
    (u : Payoff m n d) (anchor : Mixed m) : AlgorithmicFiniteTensorTightReduction u anchor := by
  sorry

end

end Blackwell.RateReduction.Palomar
