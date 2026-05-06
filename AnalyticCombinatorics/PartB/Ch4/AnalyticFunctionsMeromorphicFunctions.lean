import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
# Analytic functions and meromorphic functions

Finite zero-free, pole-order, and coefficient-window bookkeeping.
-/

namespace AnalyticCombinatorics.PartB.Ch4.AnalyticFunctionsMeromorphicFunctions

def poleMultiplicityWeight (order residueScale : ℕ) : ℕ :=
  order * (residueScale + 1)

theorem poleMultiplicityWeight_samples :
    poleMultiplicityWeight 1 0 = 1 ∧
      poleMultiplicityWeight 2 3 = 8 := by
  native_decide

theorem poleMultiplicityWeight_pos
    {order : ℕ} (h : 0 < order) (residueScale : ℕ) :
    0 < poleMultiplicityWeight order residueScale := by
  unfold poleMultiplicityWeight
  exact Nat.mul_pos h (Nat.succ_pos residueScale)

/-- Principal part coefficient of a finite pole model. -/
def principalPartCoeff (order n : ℕ) : ℕ :=
  if n < order then 1 else 0

theorem principalPartCoeff_of_lt {order n : ℕ} (h : n < order) :
    principalPartCoeff order n = 1 := by
  simp [principalPartCoeff, h]

theorem principalPartCoeff_of_not_lt {order n : ℕ} (h : ¬ n < order) :
    principalPartCoeff order n = 0 := by
  simp [principalPartCoeff, h]

def meromorphicPoleOrderReady (order residueScale : ℕ) : Prop :=
  0 < poleMultiplicityWeight order residueScale

theorem meromorphicPoleOrderReady_sample :
    meromorphicPoleOrderReady 2 3 := by
  norm_num [meromorphicPoleOrderReady, poleMultiplicityWeight]

structure MeromorphicPatch where
  analyticCharts : ℕ
  poleOrders : ℕ
  residueWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def MeromorphicPatch.ready (p : MeromorphicPatch) : Prop :=
  0 < p.analyticCharts ∧
    p.poleOrders ≤ p.analyticCharts + p.residueWindow + p.slack

def sampleMeromorphicPatch : MeromorphicPatch :=
  { analyticCharts := 4
    poleOrders := 6
    residueWindow := 2
    slack := 0 }

example : sampleMeromorphicPatch.ready := by
  norm_num [MeromorphicPatch.ready, sampleMeromorphicPatch]

def meromorphicPatchListReady (data : List MeromorphicPatch) : Bool :=
  data.all fun p =>
    0 < p.analyticCharts &&
      p.poleOrders ≤ p.analyticCharts + p.residueWindow + p.slack

theorem meromorphicPatchList_readyWindow :
    meromorphicPatchListReady
      [sampleMeromorphicPatch,
       { analyticCharts := 2, poleOrders := 3,
         residueWindow := 1, slack := 0 }] = true := by
  unfold meromorphicPatchListReady sampleMeromorphicPatch
  native_decide

structure AnalyticFunctionsMeromorphicFunctionsBudgetCertificate where
  analyticWindow : ℕ
  meromorphicWindow : ℕ
  poleWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def AnalyticFunctionsMeromorphicFunctionsBudgetCertificate.controlled
    (c : AnalyticFunctionsMeromorphicFunctionsBudgetCertificate) : Prop :=
  0 < c.analyticWindow ∧
    c.poleWindow ≤ c.analyticWindow + c.meromorphicWindow + c.slack

def AnalyticFunctionsMeromorphicFunctionsBudgetCertificate.budgetControlled
    (c : AnalyticFunctionsMeromorphicFunctionsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.analyticWindow + c.meromorphicWindow + c.poleWindow + c.slack

def AnalyticFunctionsMeromorphicFunctionsBudgetCertificate.Ready
    (c : AnalyticFunctionsMeromorphicFunctionsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def AnalyticFunctionsMeromorphicFunctionsBudgetCertificate.size
    (c : AnalyticFunctionsMeromorphicFunctionsBudgetCertificate) : ℕ :=
  c.analyticWindow + c.meromorphicWindow + c.poleWindow + c.slack

theorem analyticFunctionsMeromorphicFunctions_budgetCertificate_le_size
    (c : AnalyticFunctionsMeromorphicFunctionsBudgetCertificate)
    (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  exact h.2

def sampleAnalyticFunctionsMeromorphicFunctionsBudgetCertificate :
    AnalyticFunctionsMeromorphicFunctionsBudgetCertificate :=
  { analyticWindow := 4
    meromorphicWindow := 5
    poleWindow := 7
    certificateBudgetWindow := 17
    slack := 1 }

example :
    sampleAnalyticFunctionsMeromorphicFunctionsBudgetCertificate.Ready := by
  constructor
  · norm_num
      [AnalyticFunctionsMeromorphicFunctionsBudgetCertificate.controlled,
        sampleAnalyticFunctionsMeromorphicFunctionsBudgetCertificate]
  · norm_num
      [AnalyticFunctionsMeromorphicFunctionsBudgetCertificate.budgetControlled,
        sampleAnalyticFunctionsMeromorphicFunctionsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleAnalyticFunctionsMeromorphicFunctionsBudgetCertificate.Ready := by
  constructor
  · norm_num [AnalyticFunctionsMeromorphicFunctionsBudgetCertificate.controlled,
      sampleAnalyticFunctionsMeromorphicFunctionsBudgetCertificate]
  · norm_num [AnalyticFunctionsMeromorphicFunctionsBudgetCertificate.budgetControlled,
      sampleAnalyticFunctionsMeromorphicFunctionsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleAnalyticFunctionsMeromorphicFunctionsBudgetCertificate.certificateBudgetWindow ≤
      sampleAnalyticFunctionsMeromorphicFunctionsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady
    (data : List AnalyticFunctionsMeromorphicFunctionsBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleAnalyticFunctionsMeromorphicFunctionsBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleAnalyticFunctionsMeromorphicFunctionsBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch4.AnalyticFunctionsMeromorphicFunctions
