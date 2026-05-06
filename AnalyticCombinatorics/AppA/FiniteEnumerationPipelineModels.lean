import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Finite enumeration pipeline models.

The record stores preprocessing, transfer, and extraction budgets for a
finite enumeration pipeline.
-/

namespace AnalyticCombinatorics.AppA.FiniteEnumerationPipelineModels

structure EnumerationPipelineData where
  preprocessingBudget : ℕ
  transferBudget : ℕ
  extractionBudget : ℕ
deriving DecidableEq, Repr

def preprocessingPositive (d : EnumerationPipelineData) : Prop :=
  0 < d.preprocessingBudget

def transferControlled (d : EnumerationPipelineData) : Prop :=
  d.transferBudget ≤ d.preprocessingBudget + d.extractionBudget

def enumerationPipelineReady (d : EnumerationPipelineData) : Prop :=
  preprocessingPositive d ∧ transferControlled d

def enumerationPipelineBudget (d : EnumerationPipelineData) : ℕ :=
  d.preprocessingBudget + d.transferBudget + d.extractionBudget

theorem enumerationPipelineReady.preprocessing
    {d : EnumerationPipelineData}
    (h : enumerationPipelineReady d) :
    preprocessingPositive d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem transferBudget_le_pipelineBudget (d : EnumerationPipelineData) :
    d.transferBudget ≤ enumerationPipelineBudget d := by
  unfold enumerationPipelineBudget
  omega

def sampleEnumerationPipelineData : EnumerationPipelineData :=
  { preprocessingBudget := 6, transferBudget := 8, extractionBudget := 4 }

example : enumerationPipelineReady sampleEnumerationPipelineData := by
  norm_num [enumerationPipelineReady, preprocessingPositive]
  norm_num [transferControlled, sampleEnumerationPipelineData]

example : enumerationPipelineBudget sampleEnumerationPipelineData = 18 := by
  native_decide

structure EnumerationPipelineWindow where
  preprocessingBudget : ℕ
  transferBudget : ℕ
  extractionBudget : ℕ
  certificateBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def EnumerationPipelineWindow.transferControlled (w : EnumerationPipelineWindow) : Prop :=
  w.transferBudget ≤ w.preprocessingBudget + w.extractionBudget + w.slack

def EnumerationPipelineWindow.certificateControlled (w : EnumerationPipelineWindow) : Prop :=
  w.certificateBudget ≤ w.preprocessingBudget + w.transferBudget + w.extractionBudget + w.slack

def enumerationPipelineWindowReady (w : EnumerationPipelineWindow) : Prop :=
  0 < w.preprocessingBudget ∧
    w.transferControlled ∧
    w.certificateControlled

def EnumerationPipelineWindow.certificate (w : EnumerationPipelineWindow) : ℕ :=
  w.preprocessingBudget + w.transferBudget + w.extractionBudget + w.slack

theorem enumerationPipeline_certificateBudget_le_certificate {w : EnumerationPipelineWindow}
    (h : enumerationPipelineWindowReady w) :
    w.certificateBudget ≤ w.certificate := by
  rcases h with ⟨_, _, hcert⟩
  exact hcert

def sampleEnumerationPipelineWindow : EnumerationPipelineWindow :=
  { preprocessingBudget := 6, transferBudget := 8, extractionBudget := 4, certificateBudget := 17,
    slack := 0 }

example : enumerationPipelineWindowReady sampleEnumerationPipelineWindow := by
  norm_num [enumerationPipelineWindowReady, EnumerationPipelineWindow.transferControlled,
    EnumerationPipelineWindow.certificateControlled, sampleEnumerationPipelineWindow]

example : sampleEnumerationPipelineWindow.certificate = 18 := by
  native_decide


structure FiniteEnumerationPipelineModelsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def FiniteEnumerationPipelineModelsBudgetCertificate.controlled
    (c : FiniteEnumerationPipelineModelsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def FiniteEnumerationPipelineModelsBudgetCertificate.budgetControlled
    (c : FiniteEnumerationPipelineModelsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def FiniteEnumerationPipelineModelsBudgetCertificate.Ready
    (c : FiniteEnumerationPipelineModelsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def FiniteEnumerationPipelineModelsBudgetCertificate.size
    (c : FiniteEnumerationPipelineModelsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem finiteEnumerationPipelineModels_budgetCertificate_le_size
    (c : FiniteEnumerationPipelineModelsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleFiniteEnumerationPipelineModelsBudgetCertificate :
    FiniteEnumerationPipelineModelsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleFiniteEnumerationPipelineModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [FiniteEnumerationPipelineModelsBudgetCertificate.controlled,
      sampleFiniteEnumerationPipelineModelsBudgetCertificate]
  · norm_num [FiniteEnumerationPipelineModelsBudgetCertificate.budgetControlled,
      sampleFiniteEnumerationPipelineModelsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleFiniteEnumerationPipelineModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleFiniteEnumerationPipelineModelsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleFiniteEnumerationPipelineModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [FiniteEnumerationPipelineModelsBudgetCertificate.controlled,
      sampleFiniteEnumerationPipelineModelsBudgetCertificate]
  · norm_num [FiniteEnumerationPipelineModelsBudgetCertificate.budgetControlled,
      sampleFiniteEnumerationPipelineModelsBudgetCertificate]

example :
    sampleFiniteEnumerationPipelineModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleFiniteEnumerationPipelineModelsBudgetCertificate.size := by
  apply finiteEnumerationPipelineModels_budgetCertificate_le_size
  constructor
  · norm_num [FiniteEnumerationPipelineModelsBudgetCertificate.controlled,
      sampleFiniteEnumerationPipelineModelsBudgetCertificate]
  · norm_num [FiniteEnumerationPipelineModelsBudgetCertificate.budgetControlled,
      sampleFiniteEnumerationPipelineModelsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady
    (data : List FiniteEnumerationPipelineModelsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleFiniteEnumerationPipelineModelsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleFiniteEnumerationPipelineModelsBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppA.FiniteEnumerationPipelineModels
