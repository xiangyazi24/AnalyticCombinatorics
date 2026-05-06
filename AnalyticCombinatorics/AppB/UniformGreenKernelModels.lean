import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Uniform Green kernel models.

This module records finite bookkeeping for Green kernel windows.
-/

namespace AnalyticCombinatorics.AppB.UniformGreenKernelModels

structure GreenKernelData where
  kernelPatches : ℕ
  boundaryWindow : ℕ
  kernelSlack : ℕ
deriving DecidableEq, Repr

def hasKernelPatches (d : GreenKernelData) : Prop :=
  0 < d.kernelPatches

def boundaryWindowControlled (d : GreenKernelData) : Prop :=
  d.boundaryWindow ≤ d.kernelPatches + d.kernelSlack

def greenKernelReady (d : GreenKernelData) : Prop :=
  hasKernelPatches d ∧ boundaryWindowControlled d

def greenKernelBudget (d : GreenKernelData) : ℕ :=
  d.kernelPatches + d.boundaryWindow + d.kernelSlack

theorem greenKernelReady.hasKernelPatches {d : GreenKernelData}
    (h : greenKernelReady d) :
    hasKernelPatches d ∧ boundaryWindowControlled d ∧
      d.boundaryWindow ≤ greenKernelBudget d := by
  refine ⟨h.1, h.2, ?_⟩
  unfold greenKernelBudget
  omega

theorem boundaryWindow_le_budget (d : GreenKernelData) :
    d.boundaryWindow ≤ greenKernelBudget d := by
  unfold greenKernelBudget
  omega

def sampleGreenKernelData : GreenKernelData :=
  { kernelPatches := 6, boundaryWindow := 8, kernelSlack := 3 }

example : greenKernelReady sampleGreenKernelData := by
  norm_num [greenKernelReady, hasKernelPatches]
  norm_num [boundaryWindowControlled, sampleGreenKernelData]

example : greenKernelBudget sampleGreenKernelData = 17 := by
  native_decide

structure UniformGreenKernelWindow where
  kernelWindow : ℕ
  boundaryWindow : ℕ
  kernelSlack : ℕ
  greenBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def UniformGreenKernelWindow.boundaryControlled (w : UniformGreenKernelWindow) : Prop :=
  w.boundaryWindow ≤ w.kernelWindow + w.kernelSlack + w.slack

def uniformGreenKernelWindowReady (w : UniformGreenKernelWindow) : Prop :=
  0 < w.kernelWindow ∧ w.boundaryControlled ∧
    w.greenBudget ≤ w.kernelWindow + w.boundaryWindow + w.slack

def UniformGreenKernelWindow.certificate (w : UniformGreenKernelWindow) : ℕ :=
  w.kernelWindow + w.boundaryWindow + w.kernelSlack + w.greenBudget + w.slack

theorem uniformGreenKernel_greenBudget_le_certificate (w : UniformGreenKernelWindow) :
    w.greenBudget ≤ w.certificate := by
  unfold UniformGreenKernelWindow.certificate
  omega

def sampleUniformGreenKernelWindow : UniformGreenKernelWindow :=
  { kernelWindow := 5, boundaryWindow := 7, kernelSlack := 2, greenBudget := 14, slack := 2 }

example : uniformGreenKernelWindowReady sampleUniformGreenKernelWindow := by
  norm_num [uniformGreenKernelWindowReady, UniformGreenKernelWindow.boundaryControlled,
    sampleUniformGreenKernelWindow]


structure UniformGreenKernelModelsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def UniformGreenKernelModelsBudgetCertificate.controlled
    (c : UniformGreenKernelModelsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def UniformGreenKernelModelsBudgetCertificate.budgetControlled
    (c : UniformGreenKernelModelsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def UniformGreenKernelModelsBudgetCertificate.Ready
    (c : UniformGreenKernelModelsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def UniformGreenKernelModelsBudgetCertificate.size
    (c : UniformGreenKernelModelsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem uniformGreenKernelModels_budgetCertificate_le_size
    (c : UniformGreenKernelModelsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleUniformGreenKernelModelsBudgetCertificate :
    UniformGreenKernelModelsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleUniformGreenKernelModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [UniformGreenKernelModelsBudgetCertificate.controlled,
      sampleUniformGreenKernelModelsBudgetCertificate]
  · norm_num [UniformGreenKernelModelsBudgetCertificate.budgetControlled,
      sampleUniformGreenKernelModelsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleUniformGreenKernelModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleUniformGreenKernelModelsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleUniformGreenKernelModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [UniformGreenKernelModelsBudgetCertificate.controlled,
      sampleUniformGreenKernelModelsBudgetCertificate]
  · norm_num [UniformGreenKernelModelsBudgetCertificate.budgetControlled,
      sampleUniformGreenKernelModelsBudgetCertificate]

example :
    sampleUniformGreenKernelModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleUniformGreenKernelModelsBudgetCertificate.size := by
  apply uniformGreenKernelModels_budgetCertificate_le_size
  constructor
  · norm_num [UniformGreenKernelModelsBudgetCertificate.controlled,
      sampleUniformGreenKernelModelsBudgetCertificate]
  · norm_num [UniformGreenKernelModelsBudgetCertificate.budgetControlled,
      sampleUniformGreenKernelModelsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List UniformGreenKernelModelsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleUniformGreenKernelModelsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleUniformGreenKernelModelsBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppB.UniformGreenKernelModels
