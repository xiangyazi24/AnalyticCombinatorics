import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Generating functions as analytic objects.
-/

namespace AnalyticCombinatorics.PartB.Ch4.GeneratingFunctionsAnalyticObjects

/-- Finite ordinary generating-function coefficient model. -/
def ogfCoeff (base n : ℕ) : ℕ :=
  base ^ n

/-- Finite radius-majorant audit by a geometric envelope. -/
def radiusMajorantCheck
    (coeff : ℕ → ℕ) (base N : ℕ) : Bool :=
  (List.range (N + 1)).all fun n => coeff n ≤ base ^ n

/-- Finite statement form: coefficients define an analytic object within the sampled disk. -/
def AnalyticObjectWindow (coeff : ℕ → ℕ) (base N : ℕ) : Prop :=
  radiusMajorantCheck coeff base N = true

theorem geometricOgf_analyticObjectWindow :
    AnalyticObjectWindow (ogfCoeff 2) 2 16 := by
  unfold AnalyticObjectWindow radiusMajorantCheck ogfCoeff
  native_decide

/-- Prefix coefficient sum for a sampled ordinary generating function. -/
def ogfPrefixSum (coeff : ℕ → ℕ) (N : ℕ) : ℕ :=
  (List.range (N + 1)).foldl (fun total n => total + coeff n) 0

/-- Finite prefix-sum statement for an analytic coefficient model. -/
def PrefixMassWindow (coeff : ℕ → ℕ) (N total : ℕ) : Prop :=
  ogfPrefixSum coeff N = total

theorem geometricOgf_prefixMassWindow :
    PrefixMassWindow (ogfCoeff 2) 4 31 := by
  unfold PrefixMassWindow ogfPrefixSum ogfCoeff
  native_decide

structure GeneratingFunctionsAnalyticObjectsBudgetCertificate where
  coefficientWindow : ℕ
  radiusWindow : ℕ
  analyticWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def GeneratingFunctionsAnalyticObjectsBudgetCertificate.controlled
    (c : GeneratingFunctionsAnalyticObjectsBudgetCertificate) : Prop :=
  0 < c.coefficientWindow ∧
    c.analyticWindow ≤ c.coefficientWindow + c.radiusWindow + c.slack

def GeneratingFunctionsAnalyticObjectsBudgetCertificate.budgetControlled
    (c : GeneratingFunctionsAnalyticObjectsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.coefficientWindow + c.radiusWindow + c.analyticWindow + c.slack

def GeneratingFunctionsAnalyticObjectsBudgetCertificate.Ready
    (c : GeneratingFunctionsAnalyticObjectsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def GeneratingFunctionsAnalyticObjectsBudgetCertificate.size
    (c : GeneratingFunctionsAnalyticObjectsBudgetCertificate) : ℕ :=
  c.coefficientWindow + c.radiusWindow + c.analyticWindow + c.slack

theorem generatingFunctionsAnalyticObjects_budgetCertificate_le_size
    (c : GeneratingFunctionsAnalyticObjectsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  exact h.2

def sampleGeneratingFunctionsAnalyticObjectsBudgetCertificate :
    GeneratingFunctionsAnalyticObjectsBudgetCertificate :=
  { coefficientWindow := 5
    radiusWindow := 6
    analyticWindow := 10
    certificateBudgetWindow := 22
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleGeneratingFunctionsAnalyticObjectsBudgetCertificate.Ready := by
  constructor
  · norm_num [GeneratingFunctionsAnalyticObjectsBudgetCertificate.controlled,
      sampleGeneratingFunctionsAnalyticObjectsBudgetCertificate]
  · norm_num [GeneratingFunctionsAnalyticObjectsBudgetCertificate.budgetControlled,
      sampleGeneratingFunctionsAnalyticObjectsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleGeneratingFunctionsAnalyticObjectsBudgetCertificate.certificateBudgetWindow ≤
      sampleGeneratingFunctionsAnalyticObjectsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleGeneratingFunctionsAnalyticObjectsBudgetCertificate.Ready := by
  constructor
  · norm_num [GeneratingFunctionsAnalyticObjectsBudgetCertificate.controlled,
      sampleGeneratingFunctionsAnalyticObjectsBudgetCertificate]
  · norm_num
      [GeneratingFunctionsAnalyticObjectsBudgetCertificate.budgetControlled,
        sampleGeneratingFunctionsAnalyticObjectsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady
    (data : List GeneratingFunctionsAnalyticObjectsBudgetCertificate) : Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleGeneratingFunctionsAnalyticObjectsBudgetCertificate] = true := by
  unfold budgetCertificateListReady sampleGeneratingFunctionsAnalyticObjectsBudgetCertificate
  native_decide

example :
    budgetCertificateListReady
      [sampleGeneratingFunctionsAnalyticObjectsBudgetCertificate] = true := by
  exact budgetCertificateList_readyWindow

end AnalyticCombinatorics.PartB.Ch4.GeneratingFunctionsAnalyticObjects
