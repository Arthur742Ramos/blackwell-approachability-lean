import Mathlib

set_option autoImplicit false

/-!
# A finite tight reduction from approachability to improper phi-regret

This module formalizes a finite-simplex realization of Theorem 4 of Dann,
Mansour, Mohri, Schneider, and Sivan, *Rate-Preserving Reductions for
Blackwell Approachability* (COLT 2025).  A finite convex family of bilinear
constraints is represented by its component-index simplex.  The tensor action
space is the simplex of joint component/action distributions; its action
marginal is a canonical, linear decoder.  This removes any dependence on an
ambiguous tensor decomposition.

For each mixed constraint `w`, the comparator adds `w ⊗ marginal x`.  It is
improper because it doubles the total mass of every joint-simplex action.  The
central one-step identity proves that its regret increment is exactly the
original constraint score.  Explicit lift and decode maps therefore preserve
every finite-horizon objective in both directions.

The result deliberately formalizes the finite convex-hull/simplex regime and
finite trajectory equality.  It does not claim the paper's general
infinite-dimensional setting, randomized algorithms, or asymptotic minimax
rate theory.  Its central objective, improperness, and reduction statements
require nonempty finite constraint and action index types.
-/

namespace Blackwell.RateReduction

open scoped BigOperators

noncomputable section

/-- A real coordinate vector. -/
abbrev Dist (n : Type) := n → ℝ

/-- A real table indexed by a constraint and an action coordinate. -/
abbrev Joint (m n : Type) := m → n → ℝ

/-- The finite probability simplex. -/
def simplex {n : Type} [Fintype n] (p : Dist n) : Prop :=
  (∀ i, 0 ≤ p i) ∧ (∑ i, p i) = 1

/-- A mixed finite constraint or action. -/
abbrev Mixed (n : Type) [Fintype n] := {p : Dist n // simplex p}

/-- The probability simplex on pairs of a constraint and an action. -/
def jointSimplex {m n : Type} [Fintype m] [Fintype n]
    (x : Joint m n) : Prop :=
  (∀ i j, 0 ≤ x i j) ∧ (∑ i, ∑ j, x i j) = 1

/-- A joint-simplex action in the tensor realization. -/
abbrev JointMixed (m n : Type) [Fintype m] [Fintype n] :=
  {x : Joint m n // jointSimplex x}

/-- The action marginal of a joint distribution. -/
def marginal {m n : Type} [Fintype m] (x : Joint m n) : Dist n :=
  fun j => ∑ i, x i j

/-- A rank-one tensor table. -/
def outer {m n : Type} (w : Dist m) (p : Dist n) : Joint m n :=
  fun i j => w i * p j

/-- The source comparator `phi_w(x) = x + w ⊗ marginal(x)`. -/
def shift {m n : Type} [Fintype m] (w : Dist m) (x : Joint m n) : Joint m n :=
  fun i j => x i j + outer w (marginal x) i j

lemma sum_marginal {m n : Type} [Fintype m] [Fintype n]
    (x : Joint m n) :
    (∑ j, marginal x j) = ∑ i, ∑ j, x i j := by
  simp only [marginal]
  rw [Finset.sum_comm]

lemma marginal_simplex {m n : Type} [Fintype m] [Fintype n]
    {x : Joint m n} (hx : jointSimplex x) : simplex (marginal x) := by
  constructor
  · intro j
    exact Finset.sum_nonneg fun i _ => hx.1 i j
  · rw [sum_marginal]
    exact hx.2

lemma outer_jointSimplex {m n : Type} [Fintype m] [Fintype n]
    {w : Dist m} {p : Dist n} (hw : simplex w) (hp : simplex p) :
    jointSimplex (outer w p) := by
  constructor
  · intro i j
    exact mul_nonneg (hw.1 i) (hp.1 j)
  · simp only [outer]
    rw [← Fintype.sum_mul_sum, hw.2, hp.2]
    norm_num

lemma marginal_outer {m n : Type} [Fintype m] [Fintype n]
    {w : Dist m} {p : Dist n} (hw : simplex w) :
    marginal (outer w p) = p := by
  funext j
  simp only [marginal, outer]
  calc
    (∑ i, w i * p j) = (∑ i, w i) * p j := by rw [Finset.sum_mul]
    _ = p j := by rw [hw.2, one_mul]

/-- Embed an original mixed action using a fixed anchor constraint. -/
def lift {m n : Type} [Fintype m] [Fintype n]
    (anchor : Mixed m) (p : Mixed n) : JointMixed m n :=
  ⟨outer anchor.1 p.1, outer_jointSimplex anchor.2 p.2⟩

/-- Decode a tensor action by its action marginal. -/
def decode {m n : Type} [Fintype m] [Fintype n]
    (x : JointMixed m n) : Mixed n :=
  ⟨marginal x.1, marginal_simplex x.2⟩

lemma decode_lift {m n : Type} [Fintype m] [Fintype n]
    (anchor : Mixed m) (p : Mixed n) : decode (lift anchor p) = p := by
  apply Subtype.ext
  exact marginal_outer anchor.2

lemma shift_not_jointSimplex {m n : Type} [Fintype m] [Fintype n]
    {w : Dist m} {x : Joint m n} (hw : simplex w) (hx : jointSimplex x) :
    ¬ jointSimplex (shift w x) := by
  intro hs
  have hm : simplex (marginal x) := marginal_simplex hx
  have houter : jointSimplex (outer w (marginal x)) := outer_jointSimplex hw hm
  have hsum : (∑ i, ∑ j, shift w x i j) =
      (∑ i, ∑ j, x i j) + (∑ i, ∑ j, outer w (marginal x) i j) := by
    simp only [shift]
    simp_rw [Finset.sum_add_distrib]
  rw [hs.2, hx.2, houter.2] at hsum
  norm_num at hsum

/-- Coordinates of a finite family of bilinear constraint functions. -/
abbrev Payoff (m n d : Type) := m → n → d → ℝ

/-- The reduced loss `M_B l`, where `B(x,l) = <x, M_B l>`. -/
def reducedLoss {m n d : Type} [Fintype d]
    (u : Payoff m n d) (l : Dist d) : Joint m n :=
  fun i j => -(∑ k, u i j k * l k)

/-- Flatten a joint table so that the standard finite dot product applies. -/
def flatten {m n : Type} (x : Joint m n) : m × n → ℝ :=
  fun ij => x ij.1 ij.2

/-- The linear pairing of a joint action and a reduced loss. -/
def pairing {m n : Type} [Fintype m] [Fintype n]
    (x y : Joint m n) : ℝ :=
  dotProduct (flatten x) (flatten y)

/-- The mixed original constraint score, expressed through the tensor pairing. -/
def score {m n d : Type} [Fintype m] [Fintype n] [Fintype d]
    (u : Payoff m n d) (w : Dist m) (p : Dist n) (l : Dist d) : ℝ :=
  pairing (outer w p) (-reducedLoss u l)

lemma flatten_shift {m n : Type} [Fintype m]
    (w : Dist m) (x : Joint m n) :
    flatten (shift w x) = flatten x + flatten (outer w (marginal x)) := by
  rfl

/-- The source's pointwise reduction identity. -/
theorem pairing_shift_sub_pairing_eq_score
    {m n d : Type} [Fintype m] [Fintype n] [Fintype d]
    (u : Payoff m n d) (w : Dist m) (x : Joint m n) (l : Dist d) :
    pairing x (reducedLoss u l) - pairing (shift w x) (reducedLoss u l) =
      score u w (marginal x) l := by
  simp only [score, pairing]
  rw [flatten_shift, add_dotProduct]
  change _ = dotProduct (flatten (outer w (marginal x))) (-flatten (reducedLoss u l))
  rw [dotProduct_neg]
  abel

/-- The finite-horizon approachability objective. -/
def approachSum {m n d : Type}
    [Fintype m] [Fintype n] [Fintype d] [Nonempty m] [Nonempty n]
    {T : ℕ} (u : Payoff m n d) (w : Mixed m)
    (p : Fin T → Mixed n) (l : Fin T → Dist d) : ℝ :=
  ∑ t, score u w.1 (p t).1 (l t)

/-- The finite-horizon improper phi-regret objective. -/
def regretSum {m n d : Type}
    [Fintype m] [Fintype n] [Fintype d] [Nonempty m] [Nonempty n]
    {T : ℕ} (u : Payoff m n d) (w : Mixed m)
    (x : Fin T → JointMixed m n) (l : Fin T → Dist d) : ℝ :=
  ∑ t, (pairing (x t).1 (reducedLoss u (l t)) -
    pairing (shift w.1 (x t).1) (reducedLoss u (l t)))

/-- Summing the one-step identity preserves the objective exactly. -/
theorem regretSum_eq_approachSum {m n d : Type}
    [Fintype m] [Fintype n] [Fintype d] [Nonempty m] [Nonempty n]
    {T : ℕ} (u : Payoff m n d) (w : Mixed m)
    (x : Fin T → JointMixed m n) (l : Fin T → Dist d) :
    regretSum u w x l = approachSum u w (fun t => decode (x t)) l := by
  unfold regretSum approachSum
  apply Finset.sum_congr rfl
  intro t _
  exact pairing_shift_sub_pairing_eq_score u w.1 (x t).1 (l t)

/-- Supremum form of the approachability loss.  Nonempty constraint and action
index types keep the optimization and trajectory domains inhabited. -/
def approachLoss {m n d : Type} [Fintype m] [Fintype n] [Fintype d]
    [Nonempty m] [Nonempty n]
    {T : ℕ} (u : Payoff m n d) (p : Fin T → Mixed n)
    (l : Fin T → Dist d) : ℝ :=
  sSup (Set.range fun w : Mixed m => approachSum u w p l)

/-- Supremum form of improper phi-regret. -/
def regretLoss {m n d : Type} [Fintype m] [Fintype n] [Fintype d]
    [Nonempty m] [Nonempty n]
    {T : ℕ} (u : Payoff m n d) (x : Fin T → JointMixed m n)
    (l : Fin T → Dist d) : ℝ :=
  sSup (Set.range fun w : Mixed m => regretSum u w x l)

/-- Lift every action of a finite trajectory. -/
def liftTrajectory {m n : Type} [Fintype m] [Fintype n]
    [Nonempty m] [Nonempty n]
    (anchor : Mixed m) {T : ℕ} (p : Fin T → Mixed n) : Fin T → JointMixed m n :=
  fun t => lift anchor (p t)

/-- Decode every joint action of a finite trajectory. -/
def decodeTrajectory {m n : Type} [Fintype m] [Fintype n]
    [Nonempty m] [Nonempty n]
    {T : ℕ} (x : Fin T → JointMixed m n) : Fin T → Mixed n :=
  fun t => decode (x t)

/-- Exact equality for arbitrary transformed trajectories. -/
theorem regretLoss_eq_approachLoss {m n d : Type}
    [Fintype m] [Fintype n] [Fintype d] [Nonempty m] [Nonempty n]
    {T : ℕ} (u : Payoff m n d) (x : Fin T → JointMixed m n)
    (l : Fin T → Dist d) :
    regretLoss u x l = approachLoss u (decodeTrajectory x) l := by
  change sSup (Set.range fun w : Mixed m => regretSum u w x l) =
    sSup (Set.range fun w : Mixed m => approachSum u w (fun t => decode (x t)) l)
  apply congrArg sSup
  ext z
  constructor <;> rintro ⟨w, rfl⟩
  · exact ⟨w, (regretSum_eq_approachSum u w x l).symm⟩
  · exact ⟨w, regretSum_eq_approachSum u w x l⟩

/-- Exact forward trajectory translation. -/
theorem approach_to_regret_exact {m n d : Type}
    [Fintype m] [Fintype n] [Fintype d] [Nonempty m] [Nonempty n]
    {T : ℕ} (u : Payoff m n d) (anchor : Mixed m)
    (p : Fin T → Mixed n) (l : Fin T → Dist d) :
    regretLoss u (liftTrajectory anchor p) l = approachLoss u p l := by
  rw [regretLoss_eq_approachLoss]
  congr 1
  funext t
  exact decode_lift anchor (p t)

/-- Exact reverse trajectory translation. -/
theorem regret_to_approach_exact {m n d : Type}
    [Fintype m] [Fintype n] [Fintype d] [Nonempty m] [Nonempty n]
    {T : ℕ} (u : Payoff m n d) (x : Fin T → JointMixed m n)
    (l : Fin T → Dist d) :
    approachLoss u (decodeTrajectory x) l = regretLoss u x l :=
  (regretLoss_eq_approachLoss u x l).symm

/-- The two explicit trajectory translations that witness tightness for a
supplied anchor. -/
def FiniteTensorTightReduction {m n d : Type}
    [Fintype m] [Fintype n] [Fintype d] [Nonempty m] [Nonempty n]
    (u : Payoff m n d) (anchor : Mixed m) : Prop :=
  (∀ {T : ℕ} (p : Fin T → Mixed n) (l : Fin T → Dist d),
    regretLoss u (liftTrajectory anchor p) l = approachLoss u p l) ∧
  ∀ {T : ℕ} (x : Fin T → JointMixed m n) (l : Fin T → Dist d),
    approachLoss u (decodeTrajectory x) l = regretLoss u x l

/-- The finite simplex construction is a tight reduction for each anchor. -/
theorem finiteTensorTightReduction_of_anchor
    {m n d : Type} [Fintype m] [Fintype n] [Fintype d]
    [Nonempty m] [Nonempty n]
    (u : Payoff m n d) (anchor : Mixed m) : FiniteTensorTightReduction u anchor := by
  refine ⟨?_, ?_⟩
  · intro T p l
    exact approach_to_regret_exact u anchor p l
  · intro T x l
    exact regret_to_approach_exact u x l

/-- The source comparator is genuinely improper on the joint simplex.  The
nonemptiness assumptions exclude vacuous universal quantification over empty
mixed-action spaces. -/
def shiftImproper {m n : Type} [Fintype m] [Fintype n]
    [Nonempty m] [Nonempty n] : Prop :=
  ∀ w : Mixed m, ∀ x : JointMixed m n, ¬ jointSimplex (shift w.1 x.1)

theorem shift_is_improper {m n : Type} [Fintype m] [Fintype n]
    [Nonempty m] [Nonempty n] :
    shiftImproper (m := m) (n := n) := by
  intro w x
  exact shift_not_jointSimplex w.2 x.2

/-- A deterministic online strategy is a function of the already-observed
loss history. -/
abbrev OnlineStrategy (A L : Type) := List L → A

/-- The action played at each round against a concrete finite loss history. -/
def runTrajectory {A L : Type} (alg : OnlineStrategy A L)
    (losses : List L) : Fin losses.length → A :=
  fun t => alg (losses.take t.1)

def lossTrajectory {L : Type} (losses : List L) : Fin losses.length → L :=
  fun t => losses.get t

def liftStrategy {m n d : Type} [Fintype m] [Fintype n]
    [Nonempty m] [Nonempty n]
    (anchor : Mixed m) (alg : OnlineStrategy (Mixed n) (Dist d)) :
    OnlineStrategy (JointMixed m n) (Dist d) :=
  fun history => lift anchor (alg history)

def decodeStrategy {m n d : Type} [Fintype m] [Fintype n]
    [Nonempty m] [Nonempty n]
    (alg : OnlineStrategy (JointMixed m n) (Dist d)) :
    OnlineStrategy (Mixed n) (Dist d) :=
  fun history => decode (alg history)

theorem runTrajectory_liftStrategy {m n d : Type} [Fintype m] [Fintype n]
    [Nonempty m] [Nonempty n]
    (anchor : Mixed m) (alg : OnlineStrategy (Mixed n) (Dist d))
    (losses : List (Dist d)) :
    runTrajectory (liftStrategy anchor alg) losses =
      liftTrajectory anchor (runTrajectory alg losses) := by
  rfl

theorem runTrajectory_decodeStrategy {m n d : Type} [Fintype m] [Fintype n]
    [Nonempty m] [Nonempty n]
    (alg : OnlineStrategy (JointMixed m n) (Dist d))
    (losses : List (Dist d)) :
    runTrajectory (decodeStrategy alg) losses =
      decodeTrajectory (runTrajectory alg losses) := by
  rfl

def onlineApproachLoss {m n d : Type}
    [Fintype m] [Fintype n] [Fintype d] [Nonempty m] [Nonempty n]
    (u : Payoff m n d) (alg : OnlineStrategy (Mixed n) (Dist d))
    (losses : List (Dist d)) : ℝ :=
  approachLoss u (runTrajectory alg losses) (lossTrajectory losses)

def onlineRegretLoss {m n d : Type}
    [Fintype m] [Fintype n] [Fintype d] [Nonempty m] [Nonempty n]
    (u : Payoff m n d) (alg : OnlineStrategy (JointMixed m n) (Dist d))
    (losses : List (Dist d)) : ℝ :=
  regretLoss u (runTrajectory alg losses) (lossTrajectory losses)

theorem online_approach_to_regret_exact {m n d : Type}
    [Fintype m] [Fintype n] [Fintype d] [Nonempty m] [Nonempty n]
    (u : Payoff m n d) (anchor : Mixed m)
    (alg : OnlineStrategy (Mixed n) (Dist d)) (losses : List (Dist d)) :
    onlineRegretLoss u (liftStrategy anchor alg) losses =
      onlineApproachLoss u alg losses := by
  unfold onlineRegretLoss onlineApproachLoss
  rw [runTrajectory_liftStrategy]
  exact approach_to_regret_exact u anchor (runTrajectory alg losses) (lossTrajectory losses)

theorem online_regret_to_approach_exact {m n d : Type}
    [Fintype m] [Fintype n] [Fintype d] [Nonempty m] [Nonempty n]
    (u : Payoff m n d) (alg : OnlineStrategy (JointMixed m n) (Dist d))
    (losses : List (Dist d)) :
    onlineApproachLoss u (decodeStrategy alg) losses =
      onlineRegretLoss u alg losses := by
  unfold onlineApproachLoss onlineRegretLoss
  rw [runTrajectory_decodeStrategy]
  exact regret_to_approach_exact u (runTrajectory alg losses) (lossTrajectory losses)

/-- Algorithm-level tightness: both maps consume precisely the same prior-loss
history and preserve every finite sequence's loss. -/
def AlgorithmicFiniteTensorTightReduction {m n d : Type}
    [Fintype m] [Fintype n] [Fintype d] [Nonempty m] [Nonempty n]
    (u : Payoff m n d)
    (anchor : Mixed m) : Prop :=
  (∀ alg losses,
    onlineRegretLoss u (liftStrategy anchor alg) losses = onlineApproachLoss u alg losses) ∧
  ∀ alg losses,
    onlineApproachLoss u (decodeStrategy alg) losses = onlineRegretLoss u alg losses

/-- The finite simplex construction is tight at the level of causal online
strategies, not only preselected trajectories. -/
theorem algorithmicFiniteTensorTightReduction_of_anchor {m n d : Type}
    [Fintype m] [Fintype n] [Fintype d] [Nonempty m] [Nonempty n]
    (u : Payoff m n d) (anchor : Mixed m) : AlgorithmicFiniteTensorTightReduction u anchor := by
  refine ⟨?_, ?_⟩
  · intro alg losses
    exact online_approach_to_regret_exact u anchor alg losses
  · intro alg losses
    exact online_regret_to_approach_exact u alg losses

end

end Blackwell.RateReduction
