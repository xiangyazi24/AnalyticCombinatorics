import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Uniform contour shift models.

The finite abstraction records shift width, pole budget, and horizontal
slack.
-/

namespace AnalyticCombinatorics.AppB.UniformContourShiftModels

structure UniformContourShiftData where
  shiftWidth : ℕ
  poleBudget : ℕ
  horizontalSlack : ℕ
deriving DecidableEq, Repr

def shiftWidthPositive (d : UniformContourShiftData) : Prop :=
  0 < d.shiftWidth

def polesControlled (d : UniformContourShiftData) : Prop :=
  d.poleBudget ≤ d.shiftWidth + d.horizontalSlack

def uniformContourShiftReady (d : UniformContourShiftData) : Prop :=
  shiftWidthPositive d ∧ polesControlled d

def uniformContourShiftBudget (d : UniformContourShiftData) : ℕ :=
  d.shiftWidth + d.poleBudget + d.horizontalSlack

theorem uniformContourShiftReady.width {d : UniformContourShiftData}
    (h : uniformContourShiftReady d) :
    shiftWidthPositive d ∧ polesControlled d ∧
      d.poleBudget ≤ uniformContourShiftBudget d := by
  refine ⟨h.1, h.2, ?_⟩
  unfold uniformContourShiftBudget
  omega

theorem poleBudget_le_contourShiftBudget (d : UniformContourShiftData) :
    d.poleBudget ≤ uniformContourShiftBudget d := by
  unfold uniformContourShiftBudget
  omega

def sampleUniformContourShiftData : UniformContourShiftData :=
  { shiftWidth := 5, poleBudget := 7, horizontalSlack := 3 }

example : uniformContourShiftReady sampleUniformContourShiftData := by
  norm_num [uniformContourShiftReady, shiftWidthPositive]
  norm_num [polesControlled, sampleUniformContourShiftData]

example : uniformContourShiftBudget sampleUniformContourShiftData = 15 := by
  native_decide

/-- Finite executable readiness audit for contour-shift windows. -/
def contourShiftListReady (windows : List UniformContourShiftData) : Bool :=
  windows.all fun d =>
    0 < d.shiftWidth && d.poleBudget ≤ d.shiftWidth + d.horizontalSlack

theorem contourShiftList_readyWindow :
    contourShiftListReady
      [{ shiftWidth := 3, poleBudget := 4, horizontalSlack := 1 },
       { shiftWidth := 5, poleBudget := 7, horizontalSlack := 3 }] = true := by
  unfold contourShiftListReady
  native_decide


structure UniformContourShiftModelsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def UniformContourShiftModelsBudgetCertificate.controlled
    (c : UniformContourShiftModelsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def UniformContourShiftModelsBudgetCertificate.budgetControlled
    (c : UniformContourShiftModelsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def UniformContourShiftModelsBudgetCertificate.Ready
    (c : UniformContourShiftModelsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def UniformContourShiftModelsBudgetCertificate.size
    (c : UniformContourShiftModelsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem uniformContourShiftModels_budgetCertificate_le_size
    (c : UniformContourShiftModelsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleUniformContourShiftModelsBudgetCertificate :
    UniformContourShiftModelsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleUniformContourShiftModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [UniformContourShiftModelsBudgetCertificate.controlled,
      sampleUniformContourShiftModelsBudgetCertificate]
  · norm_num [UniformContourShiftModelsBudgetCertificate.budgetControlled,
      sampleUniformContourShiftModelsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleUniformContourShiftModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleUniformContourShiftModelsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleUniformContourShiftModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [UniformContourShiftModelsBudgetCertificate.controlled,
      sampleUniformContourShiftModelsBudgetCertificate]
  · norm_num [UniformContourShiftModelsBudgetCertificate.budgetControlled,
      sampleUniformContourShiftModelsBudgetCertificate]

example :
    sampleUniformContourShiftModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleUniformContourShiftModelsBudgetCertificate.size := by
  apply uniformContourShiftModels_budgetCertificate_le_size
  constructor
  · norm_num [UniformContourShiftModelsBudgetCertificate.controlled,
      sampleUniformContourShiftModelsBudgetCertificate]
  · norm_num [UniformContourShiftModelsBudgetCertificate.budgetControlled,
      sampleUniformContourShiftModelsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady
    (data : List UniformContourShiftModelsBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleUniformContourShiftModelsBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleUniformContourShiftModelsBudgetCertificate
  native_decide
end AnalyticCombinatorics.AppB.UniformContourShiftModels
