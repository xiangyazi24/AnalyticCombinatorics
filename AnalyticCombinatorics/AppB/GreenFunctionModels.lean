import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Green-function bookkeeping models.

The analytic Green function is represented by pole strength, boundary
control, and positivity budgets.
-/

namespace AnalyticCombinatorics.AppB.GreenFunctionModels

structure GreenDatum where
  poleStrength : ℕ
  boundaryBudget : ℕ
  positivityMargin : ℕ
deriving DecidableEq, Repr

def positivePoleStrength (g : GreenDatum) : Prop :=
  0 < g.poleStrength

def greenBoundaryControlled (g : GreenDatum) : Prop :=
  g.positivityMargin ≤ g.boundaryBudget

def greenFunctionReady (g : GreenDatum) : Prop :=
  positivePoleStrength g ∧ greenBoundaryControlled g

def greenBudget (g : GreenDatum) : ℕ :=
  g.poleStrength + g.boundaryBudget + g.positivityMargin

theorem greenFunctionReady.pole {g : GreenDatum}
    (h : greenFunctionReady g) :
    positivePoleStrength g ∧ greenBoundaryControlled g ∧
      g.poleStrength ≤ greenBudget g := by
  refine ⟨h.1, h.2, ?_⟩
  unfold greenBudget
  omega

theorem poleStrength_le_greenBudget (g : GreenDatum) :
    g.poleStrength ≤ greenBudget g := by
  unfold greenBudget
  omega

def sampleGreen : GreenDatum :=
  { poleStrength := 2, boundaryBudget := 8, positivityMargin := 3 }

example : greenFunctionReady sampleGreen := by
  norm_num [greenFunctionReady, positivePoleStrength, greenBoundaryControlled, sampleGreen]

example : greenBudget sampleGreen = 13 := by
  native_decide

structure GreenFunctionWindow where
  poleWindow : ℕ
  boundaryWindow : ℕ
  positivityWindow : ℕ
  kernelBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def GreenFunctionWindow.positivityControlled (w : GreenFunctionWindow) : Prop :=
  w.positivityWindow ≤ w.boundaryWindow + w.slack

def greenFunctionWindowReady (w : GreenFunctionWindow) : Prop :=
  0 < w.poleWindow ∧ w.positivityControlled ∧
    w.kernelBudget ≤ w.poleWindow + w.boundaryWindow + w.positivityWindow + w.slack

def GreenFunctionWindow.certificate (w : GreenFunctionWindow) : ℕ :=
  w.poleWindow + w.boundaryWindow + w.positivityWindow + w.kernelBudget + w.slack

theorem greenFunction_kernelBudget_le_certificate (w : GreenFunctionWindow) :
    w.kernelBudget ≤ w.certificate := by
  unfold GreenFunctionWindow.certificate
  omega

def sampleGreenFunctionWindow : GreenFunctionWindow :=
  { poleWindow := 2, boundaryWindow := 8, positivityWindow := 3, kernelBudget := 14, slack := 1 }

example : greenFunctionWindowReady sampleGreenFunctionWindow := by
  norm_num [greenFunctionWindowReady, GreenFunctionWindow.positivityControlled,
    sampleGreenFunctionWindow]


structure GreenFunctionModelsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def GreenFunctionModelsBudgetCertificate.controlled
    (c : GreenFunctionModelsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def GreenFunctionModelsBudgetCertificate.budgetControlled
    (c : GreenFunctionModelsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def GreenFunctionModelsBudgetCertificate.Ready
    (c : GreenFunctionModelsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def GreenFunctionModelsBudgetCertificate.size
    (c : GreenFunctionModelsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem greenFunctionModels_budgetCertificate_le_size
    (c : GreenFunctionModelsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleGreenFunctionModelsBudgetCertificate :
    GreenFunctionModelsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleGreenFunctionModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [GreenFunctionModelsBudgetCertificate.controlled,
      sampleGreenFunctionModelsBudgetCertificate]
  · norm_num [GreenFunctionModelsBudgetCertificate.budgetControlled,
      sampleGreenFunctionModelsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleGreenFunctionModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleGreenFunctionModelsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleGreenFunctionModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [GreenFunctionModelsBudgetCertificate.controlled,
      sampleGreenFunctionModelsBudgetCertificate]
  · norm_num [GreenFunctionModelsBudgetCertificate.budgetControlled,
      sampleGreenFunctionModelsBudgetCertificate]

example :
    sampleGreenFunctionModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleGreenFunctionModelsBudgetCertificate.size := by
  apply greenFunctionModels_budgetCertificate_le_size
  constructor
  · norm_num [GreenFunctionModelsBudgetCertificate.controlled,
      sampleGreenFunctionModelsBudgetCertificate]
  · norm_num [GreenFunctionModelsBudgetCertificate.budgetControlled,
      sampleGreenFunctionModelsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List GreenFunctionModelsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleGreenFunctionModelsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleGreenFunctionModelsBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppB.GreenFunctionModels
