import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
# Generating functions as analytic objects

Finite coefficient envelopes and disk-window certificates for treating
generating functions as analytic objects.
-/

namespace AnalyticCombinatorics.PartB.Ch4.GeneratingFunctionsAsAnalyticObjects

/-- A finite analytic coefficient sample. -/
structure AnalyticCoefficientSample where
  index : ℕ
  coefficientNorm : ℕ
  envelope : ℕ
deriving DecidableEq, Repr

def AnalyticCoefficientSample.controlled
    (s : AnalyticCoefficientSample) : Prop :=
  s.coefficientNorm ≤ s.envelope

def geometricEnvelope (base n : ℕ) : ℕ :=
  base ^ n

def coefficientEnvelopeReady (base N : ℕ) : Bool :=
  (List.range (N + 1)).all fun n =>
    geometricEnvelope base n ≤ geometricEnvelope base (n + 1)

theorem coefficientEnvelopeReady_samples :
    coefficientEnvelopeReady 2 12 = true ∧
      coefficientEnvelopeReady 3 8 = true := by
  unfold coefficientEnvelopeReady geometricEnvelope
  native_decide

/-- Finite disk window for analytic coefficient extraction. -/
structure AnalyticDiskWindow where
  radiusScale : ℕ
  coefficientWindow : ℕ
  envelopeWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def AnalyticDiskWindow.ready (w : AnalyticDiskWindow) : Prop :=
  0 < w.radiusScale ∧
    w.coefficientWindow ≤ w.envelopeWindow + w.slack

def sampleAnalyticDiskWindow : AnalyticDiskWindow :=
  { radiusScale := 2
    coefficientWindow := 5
    envelopeWindow := 6
    slack := 0 }

example : sampleAnalyticDiskWindow.ready := by
  norm_num [AnalyticDiskWindow.ready, sampleAnalyticDiskWindow]

def analyticDiskWindowListReady
    (data : List AnalyticDiskWindow) : Bool :=
  data.all fun w =>
    0 < w.radiusScale &&
      w.coefficientWindow ≤ w.envelopeWindow + w.slack

theorem analyticDiskWindowList_readyWindow :
    analyticDiskWindowListReady
      [sampleAnalyticDiskWindow,
       { radiusScale := 3, coefficientWindow := 4,
         envelopeWindow := 4, slack := 0 }] = true := by
  unfold analyticDiskWindowListReady sampleAnalyticDiskWindow
  native_decide

structure GeneratingFunctionsAsAnalyticObjectsBudgetCertificate where
  diskWindow : ℕ
  coefficientWindow : ℕ
  envelopeWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def GeneratingFunctionsAsAnalyticObjectsBudgetCertificate.controlled
    (c : GeneratingFunctionsAsAnalyticObjectsBudgetCertificate) : Prop :=
  0 < c.diskWindow ∧
    c.coefficientWindow ≤ c.envelopeWindow + c.slack

def GeneratingFunctionsAsAnalyticObjectsBudgetCertificate.budgetControlled
    (c : GeneratingFunctionsAsAnalyticObjectsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.diskWindow + c.coefficientWindow + c.envelopeWindow + c.slack

def GeneratingFunctionsAsAnalyticObjectsBudgetCertificate.Ready
    (c : GeneratingFunctionsAsAnalyticObjectsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def GeneratingFunctionsAsAnalyticObjectsBudgetCertificate.size
    (c : GeneratingFunctionsAsAnalyticObjectsBudgetCertificate) : ℕ :=
  c.diskWindow + c.coefficientWindow + c.envelopeWindow + c.slack

theorem generatingFunctionsAsAnalyticObjects_budgetCertificate_le_size
    (c : GeneratingFunctionsAsAnalyticObjectsBudgetCertificate)
    (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  exact h.2

def sampleGeneratingFunctionsAsAnalyticObjectsBudgetCertificate :
    GeneratingFunctionsAsAnalyticObjectsBudgetCertificate :=
  { diskWindow := 3
    coefficientWindow := 5
    envelopeWindow := 6
    certificateBudgetWindow := 15
    slack := 1 }

example :
    sampleGeneratingFunctionsAsAnalyticObjectsBudgetCertificate.Ready := by
  constructor
  · norm_num
      [GeneratingFunctionsAsAnalyticObjectsBudgetCertificate.controlled,
        sampleGeneratingFunctionsAsAnalyticObjectsBudgetCertificate]
  · norm_num
      [GeneratingFunctionsAsAnalyticObjectsBudgetCertificate.budgetControlled,
        sampleGeneratingFunctionsAsAnalyticObjectsBudgetCertificate]

theorem sampleBudgetCertificate_ready :
    sampleGeneratingFunctionsAsAnalyticObjectsBudgetCertificate.Ready := by
  constructor
  · norm_num [GeneratingFunctionsAsAnalyticObjectsBudgetCertificate.controlled,
      sampleGeneratingFunctionsAsAnalyticObjectsBudgetCertificate]
  · norm_num [GeneratingFunctionsAsAnalyticObjectsBudgetCertificate.budgetControlled,
      sampleGeneratingFunctionsAsAnalyticObjectsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleGeneratingFunctionsAsAnalyticObjectsBudgetCertificate.certificateBudgetWindow ≤
      sampleGeneratingFunctionsAsAnalyticObjectsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady
    (data : List GeneratingFunctionsAsAnalyticObjectsBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleGeneratingFunctionsAsAnalyticObjectsBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleGeneratingFunctionsAsAnalyticObjectsBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch4.GeneratingFunctionsAsAnalyticObjects
