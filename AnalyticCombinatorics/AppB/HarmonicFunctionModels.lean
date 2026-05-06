import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Discrete harmonic-function bookkeeping.

The analytic mean-value property is represented by finite neighbor sums and
integer averages.
-/

namespace AnalyticCombinatorics.AppB.HarmonicFunctionModels

structure MeanValueDatum where
  centerValue : ℕ
  neighborSum : ℕ
  neighborCount : ℕ
deriving DecidableEq, Repr

def positiveNeighborCount (d : MeanValueDatum) : Prop :=
  0 < d.neighborCount

def meanValueExact (d : MeanValueDatum) : Prop :=
  d.centerValue * d.neighborCount = d.neighborSum

def harmonicDatumReady (d : MeanValueDatum) : Prop :=
  positiveNeighborCount d ∧ meanValueExact d

def meanValueDefect (d : MeanValueDatum) : ℕ :=
  d.neighborSum - d.centerValue * d.neighborCount

theorem harmonicDatumReady.exact {d : MeanValueDatum}
    (h : harmonicDatumReady d) :
    positiveNeighborCount d ∧ meanValueExact d := by
  refine ⟨h.1, h.2⟩

theorem meanValueDefect_zero {d : MeanValueDatum}
    (h : meanValueExact d) :
    meanValueDefect d = 0 := by
  unfold meanValueDefect meanValueExact at *
  rw [← h]
  simp

def sampleMeanValue : MeanValueDatum :=
  { centerValue := 3, neighborSum := 12, neighborCount := 4 }

example : harmonicDatumReady sampleMeanValue := by
  norm_num [harmonicDatumReady, positiveNeighborCount, meanValueExact, sampleMeanValue]

example : meanValueDefect sampleMeanValue = 0 := by
  native_decide

structure HarmonicMeanValueWindow where
  centerValue : ℕ
  neighborSum : ℕ
  neighborCount : ℕ
  defectBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def HarmonicMeanValueWindow.sumControlled (w : HarmonicMeanValueWindow) : Prop :=
  w.neighborSum ≤ w.centerValue * w.neighborCount + w.defectBudget + w.slack

def HarmonicMeanValueWindow.defectControlled (w : HarmonicMeanValueWindow) : Prop :=
  w.defectBudget ≤ w.neighborSum + w.centerValue + w.neighborCount + w.slack

def harmonicMeanValueWindowReady (w : HarmonicMeanValueWindow) : Prop :=
  0 < w.neighborCount ∧
    w.sumControlled ∧
    w.defectControlled

def HarmonicMeanValueWindow.certificate (w : HarmonicMeanValueWindow) : ℕ :=
  w.neighborSum + w.centerValue + w.neighborCount + w.slack

theorem harmonic_defectBudget_le_certificate {w : HarmonicMeanValueWindow}
    (h : harmonicMeanValueWindowReady w) :
    w.defectBudget ≤ w.certificate := by
  rcases h with ⟨_, _, hdefect⟩
  exact hdefect

def sampleHarmonicMeanValueWindow : HarmonicMeanValueWindow :=
  { centerValue := 3, neighborSum := 12, neighborCount := 4, defectBudget := 1, slack := 0 }

example : harmonicMeanValueWindowReady sampleHarmonicMeanValueWindow := by
  norm_num [harmonicMeanValueWindowReady, HarmonicMeanValueWindow.sumControlled,
    HarmonicMeanValueWindow.defectControlled, sampleHarmonicMeanValueWindow]

example : sampleHarmonicMeanValueWindow.certificate = 19 := by
  native_decide


structure HarmonicFunctionModelsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def HarmonicFunctionModelsBudgetCertificate.controlled
    (c : HarmonicFunctionModelsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def HarmonicFunctionModelsBudgetCertificate.budgetControlled
    (c : HarmonicFunctionModelsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def HarmonicFunctionModelsBudgetCertificate.Ready
    (c : HarmonicFunctionModelsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def HarmonicFunctionModelsBudgetCertificate.size
    (c : HarmonicFunctionModelsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem harmonicFunctionModels_budgetCertificate_le_size
    (c : HarmonicFunctionModelsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleHarmonicFunctionModelsBudgetCertificate :
    HarmonicFunctionModelsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleHarmonicFunctionModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [HarmonicFunctionModelsBudgetCertificate.controlled,
      sampleHarmonicFunctionModelsBudgetCertificate]
  · norm_num [HarmonicFunctionModelsBudgetCertificate.budgetControlled,
      sampleHarmonicFunctionModelsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleHarmonicFunctionModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleHarmonicFunctionModelsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleHarmonicFunctionModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [HarmonicFunctionModelsBudgetCertificate.controlled,
      sampleHarmonicFunctionModelsBudgetCertificate]
  · norm_num [HarmonicFunctionModelsBudgetCertificate.budgetControlled,
      sampleHarmonicFunctionModelsBudgetCertificate]

example :
    sampleHarmonicFunctionModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleHarmonicFunctionModelsBudgetCertificate.size := by
  apply harmonicFunctionModels_budgetCertificate_le_size
  constructor
  · norm_num [HarmonicFunctionModelsBudgetCertificate.controlled,
      sampleHarmonicFunctionModelsBudgetCertificate]
  · norm_num [HarmonicFunctionModelsBudgetCertificate.budgetControlled,
      sampleHarmonicFunctionModelsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List HarmonicFunctionModelsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleHarmonicFunctionModelsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleHarmonicFunctionModelsBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppB.HarmonicFunctionModels
