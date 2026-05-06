import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Finite Jensen-formula bookkeeping.

The analytic formula relates boundary growth to zeros inside disks; this
file records the integer-side zero and boundary budgets.
-/

namespace AnalyticCombinatorics.AppB.JensenFormulaModels

structure JensenDatum where
  zerosInside : ℕ
  boundaryBudget : ℕ
  centerValueBudget : ℕ
deriving DecidableEq, Repr

def jensenDominated (d : JensenDatum) : Prop :=
  d.zerosInside + d.centerValueBudget ≤ d.boundaryBudget

def zeroBudgetSlack (d : JensenDatum) : ℕ :=
  d.boundaryBudget - (d.zerosInside + d.centerValueBudget)

theorem jensenDominated.zeros_le {d : JensenDatum}
    (h : jensenDominated d) :
    d.zerosInside ≤ d.boundaryBudget := by
  unfold jensenDominated at h
  omega

theorem zeroBudgetSlack_add {d : JensenDatum}
    (h : jensenDominated d) :
    zeroBudgetSlack d + (d.zerosInside + d.centerValueBudget) = d.boundaryBudget := by
  unfold zeroBudgetSlack jensenDominated at *
  omega

def sampleJensen : JensenDatum :=
  { zerosInside := 3, boundaryBudget := 10, centerValueBudget := 2 }

example : jensenDominated sampleJensen := by
  norm_num [jensenDominated, sampleJensen]

example : zeroBudgetSlack sampleJensen = 5 := by
  native_decide

structure JensenWindow where
  radiusIndex : ℕ
  zerosInside : ℕ
  boundaryBudget : ℕ
  centerBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def JensenWindow.ready (w : JensenWindow) : Prop :=
  w.zerosInside + w.centerBudget ≤ w.boundaryBudget + w.slack

def JensenWindow.nonzeroRadius (w : JensenWindow) : Prop :=
  0 < w.radiusIndex

def JensenWindow.certificate (w : JensenWindow) : ℕ :=
  w.radiusIndex + w.zerosInside + w.boundaryBudget + w.centerBudget + w.slack

theorem zerosInside_le_certificate (w : JensenWindow) :
    w.zerosInside ≤ w.certificate := by
  unfold JensenWindow.certificate
  omega

def sampleJensenWindow : JensenWindow :=
  { radiusIndex := 2, zerosInside := 3, boundaryBudget := 10, centerBudget := 2, slack := 0 }

example : sampleJensenWindow.ready := by
  norm_num [sampleJensenWindow, JensenWindow.ready]

example : sampleJensenWindow.nonzeroRadius := by
  norm_num [sampleJensenWindow, JensenWindow.nonzeroRadius]


structure JensenFormulaModelsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def JensenFormulaModelsBudgetCertificate.controlled
    (c : JensenFormulaModelsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def JensenFormulaModelsBudgetCertificate.budgetControlled
    (c : JensenFormulaModelsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def JensenFormulaModelsBudgetCertificate.Ready
    (c : JensenFormulaModelsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def JensenFormulaModelsBudgetCertificate.size
    (c : JensenFormulaModelsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem jensenFormulaModels_budgetCertificate_le_size
    (c : JensenFormulaModelsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleJensenFormulaModelsBudgetCertificate :
    JensenFormulaModelsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleJensenFormulaModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [JensenFormulaModelsBudgetCertificate.controlled,
      sampleJensenFormulaModelsBudgetCertificate]
  · norm_num [JensenFormulaModelsBudgetCertificate.budgetControlled,
      sampleJensenFormulaModelsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleJensenFormulaModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleJensenFormulaModelsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleJensenFormulaModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [JensenFormulaModelsBudgetCertificate.controlled,
      sampleJensenFormulaModelsBudgetCertificate]
  · norm_num [JensenFormulaModelsBudgetCertificate.budgetControlled,
      sampleJensenFormulaModelsBudgetCertificate]

example :
    sampleJensenFormulaModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleJensenFormulaModelsBudgetCertificate.size := by
  apply jensenFormulaModels_budgetCertificate_le_size
  constructor
  · norm_num [JensenFormulaModelsBudgetCertificate.controlled,
      sampleJensenFormulaModelsBudgetCertificate]
  · norm_num [JensenFormulaModelsBudgetCertificate.budgetControlled,
      sampleJensenFormulaModelsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List JensenFormulaModelsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleJensenFormulaModelsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleJensenFormulaModelsBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppB.JensenFormulaModels
