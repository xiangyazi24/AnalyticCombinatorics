import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Cauchy kernel models.

The schema records denominator clearance, contour length, and numerator
budget for finite Cauchy-kernel estimates.
-/

namespace AnalyticCombinatorics.AppB.CauchyKernelModels

structure CauchyKernelData where
  denominatorClearance : ℕ
  contourLength : ℕ
  numeratorBudget : ℕ
deriving DecidableEq, Repr

def denominatorSeparated (d : CauchyKernelData) : Prop :=
  0 < d.denominatorClearance

def numeratorControlled (d : CauchyKernelData) : Prop :=
  d.numeratorBudget ≤ d.denominatorClearance + d.contourLength

def cauchyKernelReady (d : CauchyKernelData) : Prop :=
  denominatorSeparated d ∧ numeratorControlled d

def cauchyKernelBudget (d : CauchyKernelData) : ℕ :=
  d.denominatorClearance + d.contourLength + d.numeratorBudget

theorem cauchyKernelReady.denominator {d : CauchyKernelData}
    (h : cauchyKernelReady d) :
    denominatorSeparated d ∧ numeratorControlled d ∧
      d.contourLength ≤ cauchyKernelBudget d := by
  refine ⟨h.1, h.2, ?_⟩
  unfold cauchyKernelBudget
  omega

theorem contourLength_le_kernelBudget (d : CauchyKernelData) :
    d.contourLength ≤ cauchyKernelBudget d := by
  unfold cauchyKernelBudget
  omega

def sampleCauchyKernelData : CauchyKernelData :=
  { denominatorClearance := 4, contourLength := 9, numeratorBudget := 11 }

example : cauchyKernelReady sampleCauchyKernelData := by
  norm_num [cauchyKernelReady, denominatorSeparated]
  norm_num [numeratorControlled, sampleCauchyKernelData]

example : cauchyKernelBudget sampleCauchyKernelData = 24 := by
  native_decide

/-- Finite executable readiness audit for Cauchy-kernel windows. -/
def cauchyKernelListReady (windows : List CauchyKernelData) : Bool :=
  windows.all fun d =>
    0 < d.denominatorClearance &&
      d.numeratorBudget ≤ d.denominatorClearance + d.contourLength

theorem cauchyKernelList_readyWindow :
    cauchyKernelListReady
      [{ denominatorClearance := 3, contourLength := 5, numeratorBudget := 7 },
       { denominatorClearance := 4, contourLength := 9, numeratorBudget := 11 }] = true := by
  unfold cauchyKernelListReady
  native_decide


structure CauchyKernelModelsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def CauchyKernelModelsBudgetCertificate.controlled
    (c : CauchyKernelModelsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def CauchyKernelModelsBudgetCertificate.budgetControlled
    (c : CauchyKernelModelsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def CauchyKernelModelsBudgetCertificate.Ready
    (c : CauchyKernelModelsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def CauchyKernelModelsBudgetCertificate.size
    (c : CauchyKernelModelsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem cauchyKernelModels_budgetCertificate_le_size
    (c : CauchyKernelModelsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleCauchyKernelModelsBudgetCertificate :
    CauchyKernelModelsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleCauchyKernelModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [CauchyKernelModelsBudgetCertificate.controlled,
      sampleCauchyKernelModelsBudgetCertificate]
  · norm_num [CauchyKernelModelsBudgetCertificate.budgetControlled,
      sampleCauchyKernelModelsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleCauchyKernelModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleCauchyKernelModelsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleCauchyKernelModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [CauchyKernelModelsBudgetCertificate.controlled,
      sampleCauchyKernelModelsBudgetCertificate]
  · norm_num [CauchyKernelModelsBudgetCertificate.budgetControlled,
      sampleCauchyKernelModelsBudgetCertificate]

example :
    sampleCauchyKernelModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleCauchyKernelModelsBudgetCertificate.size := by
  apply cauchyKernelModels_budgetCertificate_le_size
  constructor
  · norm_num [CauchyKernelModelsBudgetCertificate.controlled,
      sampleCauchyKernelModelsBudgetCertificate]
  · norm_num [CauchyKernelModelsBudgetCertificate.budgetControlled,
      sampleCauchyKernelModelsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady
    (data : List CauchyKernelModelsBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleCauchyKernelModelsBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleCauchyKernelModelsBudgetCertificate
  native_decide
end AnalyticCombinatorics.AppB.CauchyKernelModels
