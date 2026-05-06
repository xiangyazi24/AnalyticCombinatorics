import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
# Basic complex analysis
-/

namespace AnalyticCombinatorics.AppB.BasicComplexAnalysis

/-- A finite disc descriptor for local complex estimates. -/
structure DiscWindow where
  centerIndex : ℕ
  radius : ℕ
  sampleBound : ℕ
deriving DecidableEq, Repr

def DiscWindow.ready (w : DiscWindow) : Prop :=
  0 < w.radius ∧ w.centerIndex ≤ w.sampleBound + w.radius

def unitDiscWindow : DiscWindow :=
  { centerIndex := 0, radius := 1, sampleBound := 4 }

theorem unitDiscWindow_ready :
    unitDiscWindow.ready := by
  norm_num [DiscWindow.ready, unitDiscWindow]

example : unitDiscWindow.ready := by
  exact unitDiscWindow_ready

/-- Coefficient bound model from a Cauchy estimate on a sampled radius. -/
def cauchyCoefficientBound (majorant radiusPower : ℕ) : ℕ :=
  majorant * radiusPower

theorem cauchyCoefficientBound_zero_majorant (r : ℕ) :
    cauchyCoefficientBound 0 r = 0 := by
  simp [cauchyCoefficientBound]

theorem cauchyCoefficientBound_one_radius (m : ℕ) :
    cauchyCoefficientBound m 1 = m := by
  simp [cauchyCoefficientBound]

/-- Finite analytic coefficient table used by elementary examples. -/
def geometricCoeff (_n : ℕ) : ℕ :=
  1

theorem geometricCoeff_eq_one (n : ℕ) :
    geometricCoeff n = 1 := rfl

def coefficientPrefixBound (a : ℕ → ℕ) (bound N : ℕ) : Bool :=
  (List.range (N + 1)).all fun n => a n ≤ bound

theorem geometricCoeff_prefixBound (N : ℕ) :
    coefficientPrefixBound geometricCoeff 1 N = true := by
  unfold coefficientPrefixBound geometricCoeff
  simp

example : cauchyCoefficientBound 5 7 = 35 := by
  native_decide

structure BudgetCertificate where
  analyticWindow : ℕ
  contourWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def BudgetCertificate.controlled (c : BudgetCertificate) : Prop :=
  0 < c.analyticWindow ∧ c.contourWindow ≤ c.analyticWindow + c.slack

def BudgetCertificate.budgetControlled (c : BudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.analyticWindow + c.contourWindow + c.slack

def BudgetCertificate.Ready (c : BudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def BudgetCertificate.size (c : BudgetCertificate) : ℕ :=
  c.analyticWindow + c.contourWindow + c.slack

def sampleBudgetCertificate : BudgetCertificate :=
  { analyticWindow := 5, contourWindow := 6,
    certificateBudgetWindow := 12, slack := 1 }

example : sampleBudgetCertificate.Ready := by
  constructor
  · norm_num [BudgetCertificate.controlled, sampleBudgetCertificate]
  · norm_num [BudgetCertificate.budgetControlled, sampleBudgetCertificate]

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

def budgetCertificateListReady (data : List BudgetCertificate) : Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady [sampleBudgetCertificate] = true := by
  unfold budgetCertificateListReady sampleBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppB.BasicComplexAnalysis
