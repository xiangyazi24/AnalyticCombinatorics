import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Poisson-kernel bookkeeping models.

The harmonic-analysis content is represented by finite mass and denominator
budgets for boundary averages.
-/

namespace AnalyticCombinatorics.AppB.PoissonKernelModels

structure KernelAverage where
  boundaryMass : ℕ
  kernelWeight : ℕ
  denominator : ℕ
deriving DecidableEq, Repr

def positiveKernelDenominator (k : KernelAverage) : Prop :=
  0 < k.denominator

def kernelMassControlled (k : KernelAverage) : Prop :=
  k.boundaryMass * k.kernelWeight ≤ k.denominator

def poissonKernelReady (k : KernelAverage) : Prop :=
  positiveKernelDenominator k ∧ kernelMassControlled k

def kernelSlack (k : KernelAverage) : ℕ :=
  k.denominator - k.boundaryMass * k.kernelWeight

theorem poissonKernelReady.controlled {k : KernelAverage}
    (h : poissonKernelReady k) :
    positiveKernelDenominator k ∧ kernelMassControlled k := by
  refine ⟨h.1, h.2⟩

theorem kernelSlack_add {k : KernelAverage}
    (h : kernelMassControlled k) :
    kernelSlack k + k.boundaryMass * k.kernelWeight = k.denominator := by
  unfold kernelSlack kernelMassControlled at *
  omega

def sampleKernel : KernelAverage :=
  { boundaryMass := 3, kernelWeight := 2, denominator := 10 }

example : poissonKernelReady sampleKernel := by
  norm_num [poissonKernelReady, positiveKernelDenominator, kernelMassControlled, sampleKernel]

example : kernelSlack sampleKernel = 4 := by
  native_decide

structure PoissonKernelWindow where
  boundaryMass : ℕ
  kernelWeight : ℕ
  denominator : ℕ
  averagingError : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def PoissonKernelWindow.denominatorReady (w : PoissonKernelWindow) : Prop :=
  0 < w.denominator

def PoissonKernelWindow.massControlled (w : PoissonKernelWindow) : Prop :=
  w.boundaryMass * w.kernelWeight + w.averagingError ≤ w.denominator + w.slack

def PoissonKernelWindow.ready (w : PoissonKernelWindow) : Prop :=
  w.denominatorReady ∧ w.massControlled

def PoissonKernelWindow.certificate (w : PoissonKernelWindow) : ℕ :=
  w.boundaryMass + w.kernelWeight + w.denominator + w.averagingError + w.slack

theorem averagingError_le_certificate (w : PoissonKernelWindow) :
    w.averagingError ≤ w.certificate := by
  unfold PoissonKernelWindow.certificate
  omega

def samplePoissonKernelWindow : PoissonKernelWindow :=
  { boundaryMass := 3, kernelWeight := 2, denominator := 10, averagingError := 2, slack := 0 }

example : samplePoissonKernelWindow.ready := by
  norm_num [samplePoissonKernelWindow, PoissonKernelWindow.ready,
    PoissonKernelWindow.denominatorReady, PoissonKernelWindow.massControlled]


structure PoissonKernelModelsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def PoissonKernelModelsBudgetCertificate.controlled
    (c : PoissonKernelModelsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def PoissonKernelModelsBudgetCertificate.budgetControlled
    (c : PoissonKernelModelsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def PoissonKernelModelsBudgetCertificate.Ready
    (c : PoissonKernelModelsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def PoissonKernelModelsBudgetCertificate.size
    (c : PoissonKernelModelsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem poissonKernelModels_budgetCertificate_le_size
    (c : PoissonKernelModelsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def samplePoissonKernelModelsBudgetCertificate :
    PoissonKernelModelsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    samplePoissonKernelModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [PoissonKernelModelsBudgetCertificate.controlled,
      samplePoissonKernelModelsBudgetCertificate]
  · norm_num [PoissonKernelModelsBudgetCertificate.budgetControlled,
      samplePoissonKernelModelsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    samplePoissonKernelModelsBudgetCertificate.certificateBudgetWindow ≤
      samplePoissonKernelModelsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : samplePoissonKernelModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [PoissonKernelModelsBudgetCertificate.controlled,
      samplePoissonKernelModelsBudgetCertificate]
  · norm_num [PoissonKernelModelsBudgetCertificate.budgetControlled,
      samplePoissonKernelModelsBudgetCertificate]

example :
    samplePoissonKernelModelsBudgetCertificate.certificateBudgetWindow ≤
      samplePoissonKernelModelsBudgetCertificate.size := by
  apply poissonKernelModels_budgetCertificate_le_size
  constructor
  · norm_num [PoissonKernelModelsBudgetCertificate.controlled,
      samplePoissonKernelModelsBudgetCertificate]
  · norm_num [PoissonKernelModelsBudgetCertificate.budgetControlled,
      samplePoissonKernelModelsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List PoissonKernelModelsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [samplePoissonKernelModelsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady samplePoissonKernelModelsBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppB.PoissonKernelModels
