import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
# Laplace's method
-/

namespace AnalyticCombinatorics.AppB.LaplacesMethod

/-- Discrete quadratic drop from a peak, a finite Laplace-method model. -/
def quadraticDrop (peak n : ℕ) : ℕ :=
  if n ≤ peak then (peak - n) ^ 2 else (n - peak) ^ 2

theorem quadraticDrop_peak (peak : ℕ) :
    quadraticDrop peak peak = 0 := by
  simp [quadraticDrop]

theorem quadraticDrop_symmetric_left (peak d : ℕ) (h : d ≤ peak) :
    quadraticDrop peak (peak - d) = d ^ 2 := by
  have hle : peak - d ≤ peak := Nat.sub_le peak d
  have hsub : peak - (peak - d) = d := Nat.sub_sub_self h
  simp [quadraticDrop, hle, hsub]

/-- A finite peak certificate: all sampled drops are nonnegative. -/
def laplacePeakWindowReady (peak radius : ℕ) : Bool :=
  (List.range (radius + 1)).all fun d =>
    quadraticDrop peak (peak + d) = d ^ 2

theorem laplacePeakWindowReady_sample :
    laplacePeakWindowReady 5 6 = true := by
  unfold laplacePeakWindowReady quadraticDrop
  native_decide

structure BudgetCertificate where
  peakWindow : ℕ
  gaussianWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def BudgetCertificate.controlled (c : BudgetCertificate) : Prop :=
  0 < c.peakWindow ∧ c.gaussianWindow ≤ c.peakWindow + c.slack

def BudgetCertificate.budgetControlled (c : BudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.peakWindow + c.gaussianWindow + c.slack

def BudgetCertificate.Ready (c : BudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def BudgetCertificate.size (c : BudgetCertificate) : ℕ :=
  c.peakWindow + c.gaussianWindow + c.slack

def sampleBudgetCertificate : BudgetCertificate :=
  { peakWindow := 5, gaussianWindow := 6, certificateBudgetWindow := 12,
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleBudgetCertificate.Ready := by
  constructor
  · norm_num [BudgetCertificate.controlled,
      sampleBudgetCertificate]
  · norm_num [BudgetCertificate.budgetControlled,
      sampleBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleBudgetCertificate.certificateBudgetWindow ≤
      sampleBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleBudgetCertificate.Ready := by
  constructor
  · norm_num [BudgetCertificate.controlled, sampleBudgetCertificate]
  · norm_num [BudgetCertificate.budgetControlled, sampleBudgetCertificate]

def budgetCertificateListReady (data : List BudgetCertificate) : Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady [sampleBudgetCertificate] = true := by
  unfold budgetCertificateListReady sampleBudgetCertificate
  native_decide

example :
    budgetCertificateListReady
      [sampleBudgetCertificate] = true := by
  exact budgetCertificateList_readyWindow

end AnalyticCombinatorics.AppB.LaplacesMethod
