import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Subharmonic-function bookkeeping models.

The analytic mean inequality is represented by finite center and boundary
budgets.
-/

namespace AnalyticCombinatorics.AppB.SubharmonicModels

structure SubharmonicDatum where
  centerValue : ℕ
  boundaryAverageNumerator : ℕ
  boundaryAverageDenominator : ℕ
deriving DecidableEq, Repr

def positiveBoundaryDenominator (d : SubharmonicDatum) : Prop :=
  0 < d.boundaryAverageDenominator

def subMeanInequality (d : SubharmonicDatum) : Prop :=
  d.centerValue * d.boundaryAverageDenominator ≤ d.boundaryAverageNumerator

def subharmonicReady (d : SubharmonicDatum) : Prop :=
  positiveBoundaryDenominator d ∧ subMeanInequality d

def subMeanSlack (d : SubharmonicDatum) : ℕ :=
  d.boundaryAverageNumerator - d.centerValue * d.boundaryAverageDenominator

theorem subharmonicReady.mean {d : SubharmonicDatum}
    (h : subharmonicReady d) :
    positiveBoundaryDenominator d ∧ subMeanInequality d := by
  refine ⟨h.1, h.2⟩

theorem subMeanSlack_add {d : SubharmonicDatum}
    (h : subMeanInequality d) :
    subMeanSlack d + d.centerValue * d.boundaryAverageDenominator =
      d.boundaryAverageNumerator := by
  unfold subMeanSlack subMeanInequality at *
  omega

def sampleSubharmonic : SubharmonicDatum :=
  { centerValue := 3, boundaryAverageNumerator := 14, boundaryAverageDenominator := 4 }

example : subharmonicReady sampleSubharmonic := by
  norm_num [subharmonicReady, positiveBoundaryDenominator, subMeanInequality, sampleSubharmonic]

example : subMeanSlack sampleSubharmonic = 2 := by
  native_decide

structure SubharmonicWindow where
  centerValue : ℕ
  boundaryAverageNumerator : ℕ
  boundaryAverageDenominator : ℕ
  subMeanBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def SubharmonicWindow.subMeanControlled (w : SubharmonicWindow) : Prop :=
  w.centerValue * w.boundaryAverageDenominator ≤ w.boundaryAverageNumerator + w.slack

def SubharmonicWindow.budgetControlled (w : SubharmonicWindow) : Prop :=
  w.subMeanBudget ≤
    w.centerValue + w.boundaryAverageNumerator + w.boundaryAverageDenominator + w.slack

def subharmonicWindowReady (w : SubharmonicWindow) : Prop :=
  0 < w.boundaryAverageDenominator ∧
    w.subMeanControlled ∧
    w.budgetControlled

def SubharmonicWindow.certificate (w : SubharmonicWindow) : ℕ :=
  w.centerValue + w.boundaryAverageNumerator + w.boundaryAverageDenominator + w.slack

theorem subharmonic_budget_le_certificate {w : SubharmonicWindow}
    (h : subharmonicWindowReady w) :
    w.subMeanBudget ≤ w.certificate := by
  rcases h with ⟨_, _, hbudget⟩
  exact hbudget

def sampleSubharmonicWindow : SubharmonicWindow :=
  { centerValue := 3, boundaryAverageNumerator := 14, boundaryAverageDenominator := 4,
    subMeanBudget := 20, slack := 0 }

example : subharmonicWindowReady sampleSubharmonicWindow := by
  norm_num [subharmonicWindowReady, SubharmonicWindow.subMeanControlled,
    SubharmonicWindow.budgetControlled, sampleSubharmonicWindow]

example : sampleSubharmonicWindow.certificate = 21 := by
  native_decide


structure SubharmonicModelsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def SubharmonicModelsBudgetCertificate.controlled
    (c : SubharmonicModelsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def SubharmonicModelsBudgetCertificate.budgetControlled
    (c : SubharmonicModelsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def SubharmonicModelsBudgetCertificate.Ready
    (c : SubharmonicModelsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def SubharmonicModelsBudgetCertificate.size
    (c : SubharmonicModelsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem subharmonicModels_budgetCertificate_le_size
    (c : SubharmonicModelsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleSubharmonicModelsBudgetCertificate :
    SubharmonicModelsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleSubharmonicModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [SubharmonicModelsBudgetCertificate.controlled,
      sampleSubharmonicModelsBudgetCertificate]
  · norm_num [SubharmonicModelsBudgetCertificate.budgetControlled,
      sampleSubharmonicModelsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleSubharmonicModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleSubharmonicModelsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleSubharmonicModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [SubharmonicModelsBudgetCertificate.controlled,
      sampleSubharmonicModelsBudgetCertificate]
  · norm_num [SubharmonicModelsBudgetCertificate.budgetControlled,
      sampleSubharmonicModelsBudgetCertificate]

example :
    sampleSubharmonicModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleSubharmonicModelsBudgetCertificate.size := by
  apply subharmonicModels_budgetCertificate_le_size
  constructor
  · norm_num [SubharmonicModelsBudgetCertificate.controlled,
      sampleSubharmonicModelsBudgetCertificate]
  · norm_num [SubharmonicModelsBudgetCertificate.budgetControlled,
      sampleSubharmonicModelsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List SubharmonicModelsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleSubharmonicModelsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleSubharmonicModelsBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppB.SubharmonicModels
