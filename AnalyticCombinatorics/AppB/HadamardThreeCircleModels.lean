import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Hadamard three-circle bookkeeping.

The analytic convexity statement is represented by finite inner, middle,
and outer growth budgets.
-/

namespace AnalyticCombinatorics.AppB.HadamardThreeCircleModels

structure ThreeCircleDatum where
  innerBound : ℕ
  middleBound : ℕ
  outerBound : ℕ
deriving DecidableEq, Repr

def orderedBounds (d : ThreeCircleDatum) : Prop :=
  d.innerBound ≤ d.middleBound ∧ d.middleBound ≤ d.outerBound

def threeCircleReady (d : ThreeCircleDatum) : Prop :=
  orderedBounds d

def annularGrowth (d : ThreeCircleDatum) : ℕ :=
  d.outerBound - d.innerBound

theorem orderedBounds.inner_le_outer {d : ThreeCircleDatum}
    (h : orderedBounds d) :
    d.innerBound ≤ d.outerBound := le_trans h.1 h.2

theorem annularGrowth_add {d : ThreeCircleDatum}
    (h : orderedBounds d) :
    annularGrowth d + d.innerBound = d.outerBound := by
  unfold annularGrowth
  exact Nat.sub_add_cancel (h.inner_le_outer)

def sampleThreeCircle : ThreeCircleDatum :=
  { innerBound := 2, middleBound := 5, outerBound := 9 }

example : threeCircleReady sampleThreeCircle := by
  norm_num [threeCircleReady, orderedBounds, sampleThreeCircle]

example : annularGrowth sampleThreeCircle = 7 := by
  native_decide

structure ThreeCircleWindow where
  innerRadiusIndex : ℕ
  middleRadiusIndex : ℕ
  outerRadiusIndex : ℕ
  innerBound : ℕ
  middleBound : ℕ
  outerBound : ℕ
deriving DecidableEq, Repr

def ThreeCircleWindow.radiiOrdered (w : ThreeCircleWindow) : Prop :=
  w.innerRadiusIndex ≤ w.middleRadiusIndex ∧ w.middleRadiusIndex ≤ w.outerRadiusIndex

def ThreeCircleWindow.boundsOrdered (w : ThreeCircleWindow) : Prop :=
  w.innerBound ≤ w.middleBound ∧ w.middleBound ≤ w.outerBound

def ThreeCircleWindow.ready (w : ThreeCircleWindow) : Prop :=
  w.radiiOrdered ∧ w.boundsOrdered

def ThreeCircleWindow.certificate (w : ThreeCircleWindow) : ℕ :=
  w.innerRadiusIndex + w.middleRadiusIndex + w.outerRadiusIndex +
    w.innerBound + w.middleBound + w.outerBound

theorem middleBound_le_certificate (w : ThreeCircleWindow) :
    w.middleBound ≤ w.certificate := by
  unfold ThreeCircleWindow.certificate
  omega

def sampleThreeCircleWindow : ThreeCircleWindow :=
  { innerRadiusIndex := 1, middleRadiusIndex := 2, outerRadiusIndex := 3,
    innerBound := 2, middleBound := 5, outerBound := 9 }

example : sampleThreeCircleWindow.ready := by
  norm_num [sampleThreeCircleWindow, ThreeCircleWindow.ready,
    ThreeCircleWindow.radiiOrdered, ThreeCircleWindow.boundsOrdered]


structure HadamardThreeCircleModelsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def HadamardThreeCircleModelsBudgetCertificate.controlled
    (c : HadamardThreeCircleModelsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def HadamardThreeCircleModelsBudgetCertificate.budgetControlled
    (c : HadamardThreeCircleModelsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def HadamardThreeCircleModelsBudgetCertificate.Ready
    (c : HadamardThreeCircleModelsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def HadamardThreeCircleModelsBudgetCertificate.size
    (c : HadamardThreeCircleModelsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem hadamardThreeCircleModels_budgetCertificate_le_size
    (c : HadamardThreeCircleModelsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleHadamardThreeCircleModelsBudgetCertificate :
    HadamardThreeCircleModelsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleHadamardThreeCircleModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [HadamardThreeCircleModelsBudgetCertificate.controlled,
      sampleHadamardThreeCircleModelsBudgetCertificate]
  · norm_num [HadamardThreeCircleModelsBudgetCertificate.budgetControlled,
      sampleHadamardThreeCircleModelsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleHadamardThreeCircleModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleHadamardThreeCircleModelsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleHadamardThreeCircleModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [HadamardThreeCircleModelsBudgetCertificate.controlled,
      sampleHadamardThreeCircleModelsBudgetCertificate]
  · norm_num [HadamardThreeCircleModelsBudgetCertificate.budgetControlled,
      sampleHadamardThreeCircleModelsBudgetCertificate]

example :
    sampleHadamardThreeCircleModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleHadamardThreeCircleModelsBudgetCertificate.size := by
  apply hadamardThreeCircleModels_budgetCertificate_le_size
  constructor
  · norm_num [HadamardThreeCircleModelsBudgetCertificate.controlled,
      sampleHadamardThreeCircleModelsBudgetCertificate]
  · norm_num [HadamardThreeCircleModelsBudgetCertificate.budgetControlled,
      sampleHadamardThreeCircleModelsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List HadamardThreeCircleModelsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleHadamardThreeCircleModelsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleHadamardThreeCircleModelsBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppB.HadamardThreeCircleModels
