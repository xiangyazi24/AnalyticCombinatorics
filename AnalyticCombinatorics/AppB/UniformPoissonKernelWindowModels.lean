import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Uniform Poisson kernel window models.

This module records finite bookkeeping for Poisson kernel windows.
-/

namespace AnalyticCombinatorics.AppB.UniformPoissonKernelWindowModels

structure PoissonKernelWindowData where
  kernelOrder : ℕ
  boundaryWindow : ℕ
  kernelSlack : ℕ
deriving DecidableEq, Repr

def hasKernelOrder (d : PoissonKernelWindowData) : Prop :=
  0 < d.kernelOrder

def boundaryWindowControlled (d : PoissonKernelWindowData) : Prop :=
  d.boundaryWindow ≤ d.kernelOrder + d.kernelSlack

def poissonKernelWindowReady (d : PoissonKernelWindowData) : Prop :=
  hasKernelOrder d ∧ boundaryWindowControlled d

def poissonKernelWindowBudget (d : PoissonKernelWindowData) : ℕ :=
  d.kernelOrder + d.boundaryWindow + d.kernelSlack

theorem poissonKernelWindowReady.hasKernelOrder
    {d : PoissonKernelWindowData}
    (h : poissonKernelWindowReady d) :
    hasKernelOrder d ∧ boundaryWindowControlled d ∧
      d.boundaryWindow ≤ poissonKernelWindowBudget d := by
  refine ⟨h.1, h.2, ?_⟩
  unfold poissonKernelWindowBudget
  omega

theorem boundaryWindow_le_budget (d : PoissonKernelWindowData) :
    d.boundaryWindow ≤ poissonKernelWindowBudget d := by
  unfold poissonKernelWindowBudget
  omega

def samplePoissonKernelWindowData : PoissonKernelWindowData :=
  { kernelOrder := 6, boundaryWindow := 8, kernelSlack := 3 }

example : poissonKernelWindowReady samplePoissonKernelWindowData := by
  norm_num [poissonKernelWindowReady, hasKernelOrder]
  norm_num [boundaryWindowControlled, samplePoissonKernelWindowData]

example : poissonKernelWindowBudget samplePoissonKernelWindowData = 17 := by
  native_decide

/-- Finite executable readiness audit for Poisson-kernel windows. -/
def poissonKernelWindowListReady (windows : List PoissonKernelWindowData) : Bool :=
  windows.all fun d =>
    0 < d.kernelOrder && d.boundaryWindow ≤ d.kernelOrder + d.kernelSlack

theorem poissonKernelWindowList_readyWindow :
    poissonKernelWindowListReady
      [{ kernelOrder := 4, boundaryWindow := 5, kernelSlack := 1 },
       { kernelOrder := 6, boundaryWindow := 8, kernelSlack := 3 }] = true := by
  unfold poissonKernelWindowListReady
  native_decide


structure UniformPoissonKernelWindowModelsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def UniformPoissonKernelWindowModelsBudgetCertificate.controlled
    (c : UniformPoissonKernelWindowModelsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def UniformPoissonKernelWindowModelsBudgetCertificate.budgetControlled
    (c : UniformPoissonKernelWindowModelsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def UniformPoissonKernelWindowModelsBudgetCertificate.Ready
    (c : UniformPoissonKernelWindowModelsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def UniformPoissonKernelWindowModelsBudgetCertificate.size
    (c : UniformPoissonKernelWindowModelsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem uniformPoissonKernelWindowModels_budgetCertificate_le_size
    (c : UniformPoissonKernelWindowModelsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleUniformPoissonKernelWindowModelsBudgetCertificate :
    UniformPoissonKernelWindowModelsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleUniformPoissonKernelWindowModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [UniformPoissonKernelWindowModelsBudgetCertificate.controlled,
      sampleUniformPoissonKernelWindowModelsBudgetCertificate]
  · norm_num [UniformPoissonKernelWindowModelsBudgetCertificate.budgetControlled,
      sampleUniformPoissonKernelWindowModelsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleUniformPoissonKernelWindowModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleUniformPoissonKernelWindowModelsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleUniformPoissonKernelWindowModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [UniformPoissonKernelWindowModelsBudgetCertificate.controlled,
      sampleUniformPoissonKernelWindowModelsBudgetCertificate]
  · norm_num [UniformPoissonKernelWindowModelsBudgetCertificate.budgetControlled,
      sampleUniformPoissonKernelWindowModelsBudgetCertificate]

example :
    sampleUniformPoissonKernelWindowModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleUniformPoissonKernelWindowModelsBudgetCertificate.size := by
  apply uniformPoissonKernelWindowModels_budgetCertificate_le_size
  constructor
  · norm_num [UniformPoissonKernelWindowModelsBudgetCertificate.controlled,
      sampleUniformPoissonKernelWindowModelsBudgetCertificate]
  · norm_num [UniformPoissonKernelWindowModelsBudgetCertificate.budgetControlled,
      sampleUniformPoissonKernelWindowModelsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady
    (data : List UniformPoissonKernelWindowModelsBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleUniformPoissonKernelWindowModelsBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleUniformPoissonKernelWindowModelsBudgetCertificate
  native_decide
end AnalyticCombinatorics.AppB.UniformPoissonKernelWindowModels
