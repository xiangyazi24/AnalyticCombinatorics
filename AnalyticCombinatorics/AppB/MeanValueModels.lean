import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Mean-value bookkeeping models.

The analytic mean-value property is represented by a finite center value,
boundary sum, and denominator.
-/

namespace AnalyticCombinatorics.AppB.MeanValueModels

structure MeanValueDatum where
  centerValue : ℕ
  boundarySum : ℕ
  boundaryCount : ℕ
deriving DecidableEq, Repr

def positiveBoundaryCount (d : MeanValueDatum) : Prop :=
  0 < d.boundaryCount

def meanValueExact (d : MeanValueDatum) : Prop :=
  d.centerValue * d.boundaryCount = d.boundarySum

def meanValueReady (d : MeanValueDatum) : Prop :=
  positiveBoundaryCount d ∧ meanValueExact d

def meanValueDefect (d : MeanValueDatum) : ℕ :=
  d.boundarySum - d.centerValue * d.boundaryCount

theorem meanValueReady.exact {d : MeanValueDatum}
    (h : meanValueReady d) :
    positiveBoundaryCount d ∧ meanValueExact d := by
  refine ⟨h.1, h.2⟩

theorem meanValueDefect_zero {d : MeanValueDatum}
    (h : meanValueExact d) :
    meanValueDefect d = 0 := by
  unfold meanValueDefect meanValueExact at *
  rw [← h]
  simp

def sampleMeanValue : MeanValueDatum :=
  { centerValue := 4, boundarySum := 20, boundaryCount := 5 }

example : meanValueReady sampleMeanValue := by
  norm_num [meanValueReady, positiveBoundaryCount, meanValueExact, sampleMeanValue]

example : meanValueDefect sampleMeanValue = 0 := by
  native_decide

structure BoundaryMeanValueWindow where
  centerValue : ℕ
  boundarySum : ℕ
  boundaryCount : ℕ
  defectBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def BoundaryMeanValueWindow.sumControlled (w : BoundaryMeanValueWindow) : Prop :=
  w.boundarySum ≤ w.centerValue * w.boundaryCount + w.defectBudget + w.slack

def BoundaryMeanValueWindow.defectControlled (w : BoundaryMeanValueWindow) : Prop :=
  w.defectBudget ≤ w.boundarySum + w.centerValue + w.boundaryCount + w.slack

def boundaryMeanValueWindowReady (w : BoundaryMeanValueWindow) : Prop :=
  0 < w.boundaryCount ∧
    w.sumControlled ∧
    w.defectControlled

def BoundaryMeanValueWindow.certificate (w : BoundaryMeanValueWindow) : ℕ :=
  w.boundarySum + w.centerValue + w.boundaryCount + w.slack

theorem meanValue_defectBudget_le_certificate {w : BoundaryMeanValueWindow}
    (h : boundaryMeanValueWindowReady w) :
    w.defectBudget ≤ w.certificate := by
  rcases h with ⟨_, _, hdefect⟩
  exact hdefect

def sampleBoundaryMeanValueWindow : BoundaryMeanValueWindow :=
  { centerValue := 4, boundarySum := 20, boundaryCount := 5, defectBudget := 1, slack := 0 }

example : boundaryMeanValueWindowReady sampleBoundaryMeanValueWindow := by
  norm_num [boundaryMeanValueWindowReady, BoundaryMeanValueWindow.sumControlled,
    BoundaryMeanValueWindow.defectControlled, sampleBoundaryMeanValueWindow]

example : sampleBoundaryMeanValueWindow.certificate = 29 := by
  native_decide


structure MeanValueModelsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def MeanValueModelsBudgetCertificate.controlled
    (c : MeanValueModelsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def MeanValueModelsBudgetCertificate.budgetControlled
    (c : MeanValueModelsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def MeanValueModelsBudgetCertificate.Ready
    (c : MeanValueModelsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def MeanValueModelsBudgetCertificate.size
    (c : MeanValueModelsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem meanValueModels_budgetCertificate_le_size
    (c : MeanValueModelsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleMeanValueModelsBudgetCertificate :
    MeanValueModelsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleMeanValueModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [MeanValueModelsBudgetCertificate.controlled,
      sampleMeanValueModelsBudgetCertificate]
  · norm_num [MeanValueModelsBudgetCertificate.budgetControlled,
      sampleMeanValueModelsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleMeanValueModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleMeanValueModelsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleMeanValueModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [MeanValueModelsBudgetCertificate.controlled,
      sampleMeanValueModelsBudgetCertificate]
  · norm_num [MeanValueModelsBudgetCertificate.budgetControlled,
      sampleMeanValueModelsBudgetCertificate]

example :
    sampleMeanValueModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleMeanValueModelsBudgetCertificate.size := by
  apply meanValueModels_budgetCertificate_le_size
  constructor
  · norm_num [MeanValueModelsBudgetCertificate.controlled,
      sampleMeanValueModelsBudgetCertificate]
  · norm_num [MeanValueModelsBudgetCertificate.budgetControlled,
      sampleMeanValueModelsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List MeanValueModelsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleMeanValueModelsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleMeanValueModelsBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppB.MeanValueModels
