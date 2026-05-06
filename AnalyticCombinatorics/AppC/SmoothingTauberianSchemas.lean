import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Smoothing Tauberian schema bookkeeping.

The finite record stores smoothing width, kernel mass, and residual error.
-/

namespace AnalyticCombinatorics.AppC.SmoothingTauberianSchemas

structure SmoothingData where
  smoothingWidth : ℕ
  kernelMass : ℕ
  residualError : ℕ
deriving DecidableEq, Repr

def positiveSmoothingWidth (d : SmoothingData) : Prop :=
  0 < d.smoothingWidth

def positiveKernelMass (d : SmoothingData) : Prop :=
  0 < d.kernelMass

def smoothingTauberianReady (d : SmoothingData) : Prop :=
  positiveSmoothingWidth d ∧ positiveKernelMass d

def smoothingBudget (d : SmoothingData) : ℕ :=
  d.smoothingWidth + d.kernelMass + d.residualError

theorem smoothingTauberianReady.kernel {d : SmoothingData}
    (h : smoothingTauberianReady d) :
    positiveKernelMass d := by
  rcases h with ⟨hleft, hright⟩
  exact hright

theorem smoothingWidth_le_budget (d : SmoothingData) :
    d.smoothingWidth ≤ smoothingBudget d := by
  unfold smoothingBudget
  omega

def sampleSmoothing : SmoothingData :=
  { smoothingWidth := 5, kernelMass := 3, residualError := 2 }

example : smoothingTauberianReady sampleSmoothing := by
  norm_num [smoothingTauberianReady, positiveSmoothingWidth, positiveKernelMass, sampleSmoothing]

example : smoothingBudget sampleSmoothing = 10 := by
  native_decide

structure SmoothingWindow where
  smoothingWidth : ℕ
  kernelMass : ℕ
  residualError : ℕ
  smoothedMass : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def SmoothingWindow.kernelReady (w : SmoothingWindow) : Prop :=
  0 < w.smoothingWidth ∧ 0 < w.kernelMass

def SmoothingWindow.errorControlled (w : SmoothingWindow) : Prop :=
  w.residualError ≤ w.kernelMass + w.slack

def SmoothingWindow.massControlled (w : SmoothingWindow) : Prop :=
  w.smoothedMass ≤ w.smoothingWidth * w.kernelMass + w.slack

def SmoothingWindow.ready (w : SmoothingWindow) : Prop :=
  w.kernelReady ∧ w.errorControlled ∧ w.massControlled

def SmoothingWindow.certificate (w : SmoothingWindow) : ℕ :=
  w.smoothingWidth + w.kernelMass + w.residualError + w.smoothedMass + w.slack

theorem smoothedMass_le_certificate (w : SmoothingWindow) :
    w.smoothedMass ≤ w.certificate := by
  unfold SmoothingWindow.certificate
  omega

def sampleSmoothingWindow : SmoothingWindow :=
  { smoothingWidth := 5, kernelMass := 3, residualError := 2,
    smoothedMass := 12, slack := 0 }

example : sampleSmoothingWindow.ready := by
  norm_num [sampleSmoothingWindow, SmoothingWindow.ready, SmoothingWindow.kernelReady,
    SmoothingWindow.errorControlled, SmoothingWindow.massControlled]


structure SmoothingTauberianSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def SmoothingTauberianSchemasBudgetCertificate.controlled
    (c : SmoothingTauberianSchemasBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def SmoothingTauberianSchemasBudgetCertificate.budgetControlled
    (c : SmoothingTauberianSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def SmoothingTauberianSchemasBudgetCertificate.Ready
    (c : SmoothingTauberianSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def SmoothingTauberianSchemasBudgetCertificate.size
    (c : SmoothingTauberianSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem smoothingTauberianSchemas_budgetCertificate_le_size
    (c : SmoothingTauberianSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleSmoothingTauberianSchemasBudgetCertificate :
    SmoothingTauberianSchemasBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleSmoothingTauberianSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [SmoothingTauberianSchemasBudgetCertificate.controlled,
      sampleSmoothingTauberianSchemasBudgetCertificate]
  · norm_num [SmoothingTauberianSchemasBudgetCertificate.budgetControlled,
      sampleSmoothingTauberianSchemasBudgetCertificate]

example : sampleSmoothingTauberianSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [SmoothingTauberianSchemasBudgetCertificate.controlled,
      sampleSmoothingTauberianSchemasBudgetCertificate]
  · norm_num [SmoothingTauberianSchemasBudgetCertificate.budgetControlled,
      sampleSmoothingTauberianSchemasBudgetCertificate]

example :
    sampleSmoothingTauberianSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleSmoothingTauberianSchemasBudgetCertificate.size := by
  apply smoothingTauberianSchemas_budgetCertificate_le_size
  constructor
  · norm_num [SmoothingTauberianSchemasBudgetCertificate.controlled,
      sampleSmoothingTauberianSchemasBudgetCertificate]
  · norm_num [SmoothingTauberianSchemasBudgetCertificate.budgetControlled,
      sampleSmoothingTauberianSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_le_size :
    sampleSmoothingTauberianSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleSmoothingTauberianSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List SmoothingTauberianSchemasBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleSmoothingTauberianSchemasBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleSmoothingTauberianSchemasBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppC.SmoothingTauberianSchemas
