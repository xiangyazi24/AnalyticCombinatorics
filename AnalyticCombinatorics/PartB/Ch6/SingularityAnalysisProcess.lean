import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
The process of singularity analysis.

Finite pipeline bookkeeping for locating singularities, expanding locally,
and applying transfer rules.
-/

namespace AnalyticCombinatorics.PartB.Ch6.SingularityAnalysisProcess

/-- Pipeline status for a finite singularity-analysis workflow. -/
structure SingularityPipelineState where
  localized : Bool
  expanded : Bool
  transferred : Bool
deriving DecidableEq, Repr

def SingularityPipelineState.complete (s : SingularityPipelineState) : Bool :=
  s.localized && s.expanded && s.transferred

/-- Finite coefficient transfer produced by a completed pipeline. -/
def pipelineCoefficientEnvelope (complete : Bool) (n : ℕ) : ℕ :=
  if complete then (n + 1) ^ 2 else 0

def pipelineEnvelopeCheck (s : SingularityPipelineState) (N : ℕ) : Bool :=
  (List.range (N + 1)).all fun n =>
    pipelineCoefficientEnvelope s.complete n ≤ (n + 1) ^ 2

theorem completePipeline_envelope :
    pipelineEnvelopeCheck
      { localized := true, expanded := true, transferred := true } 24 = true := by
  unfold pipelineEnvelopeCheck pipelineCoefficientEnvelope
    SingularityPipelineState.complete
  native_decide

structure SingularityProcessWindow where
  localizationDepth : ℕ
  expansionDepth : ℕ
  transferDepth : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def singularityProcessReady (w : SingularityProcessWindow) : Prop :=
  0 < w.localizationDepth ∧
    w.transferDepth ≤ w.localizationDepth + w.expansionDepth + w.slack

def singularityProcessBudget (w : SingularityProcessWindow) : ℕ :=
  w.localizationDepth + w.expansionDepth + w.transferDepth + w.slack

theorem transferDepth_le_singularityProcessBudget
    (w : SingularityProcessWindow) :
    w.transferDepth ≤ singularityProcessBudget w := by
  unfold singularityProcessBudget
  omega

def sampleSingularityProcessWindow : SingularityProcessWindow :=
  { localizationDepth := 4, expansionDepth := 5, transferDepth := 8, slack := 1 }

example : singularityProcessReady sampleSingularityProcessWindow := by
  norm_num [singularityProcessReady, sampleSingularityProcessWindow]

structure SingularityAnalysisProcessBudgetCertificate where
  localizationWindow : ℕ
  expansionWindow : ℕ
  transferWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def SingularityAnalysisProcessBudgetCertificate.controlled
    (c : SingularityAnalysisProcessBudgetCertificate) : Prop :=
  0 < c.localizationWindow ∧
    c.transferWindow ≤ c.localizationWindow + c.expansionWindow + c.slack

def SingularityAnalysisProcessBudgetCertificate.budgetControlled
    (c : SingularityAnalysisProcessBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.localizationWindow + c.expansionWindow + c.transferWindow + c.slack

def SingularityAnalysisProcessBudgetCertificate.Ready
    (c : SingularityAnalysisProcessBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def SingularityAnalysisProcessBudgetCertificate.size
    (c : SingularityAnalysisProcessBudgetCertificate) : ℕ :=
  c.localizationWindow + c.expansionWindow + c.transferWindow + c.slack

theorem singularityAnalysisProcess_budgetCertificate_le_size
    (c : SingularityAnalysisProcessBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  exact h.2

def sampleSingularityAnalysisProcessBudgetCertificate :
    SingularityAnalysisProcessBudgetCertificate :=
  { localizationWindow := 4
    expansionWindow := 5
    transferWindow := 8
    certificateBudgetWindow := 18
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleSingularityAnalysisProcessBudgetCertificate.Ready := by
  constructor
  · norm_num [SingularityAnalysisProcessBudgetCertificate.controlled,
      sampleSingularityAnalysisProcessBudgetCertificate]
  · norm_num [SingularityAnalysisProcessBudgetCertificate.budgetControlled,
      sampleSingularityAnalysisProcessBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleSingularityAnalysisProcessBudgetCertificate.certificateBudgetWindow ≤
      sampleSingularityAnalysisProcessBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleSingularityAnalysisProcessBudgetCertificate.Ready := by
  constructor
  · norm_num [SingularityAnalysisProcessBudgetCertificate.controlled,
      sampleSingularityAnalysisProcessBudgetCertificate]
  · norm_num [SingularityAnalysisProcessBudgetCertificate.budgetControlled,
      sampleSingularityAnalysisProcessBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List SingularityAnalysisProcessBudgetCertificate) : Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady [sampleSingularityAnalysisProcessBudgetCertificate] = true := by
  unfold budgetCertificateListReady sampleSingularityAnalysisProcessBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch6.SingularityAnalysisProcess
