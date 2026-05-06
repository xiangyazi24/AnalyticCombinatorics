import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
# The process of singularity analysis
-/

namespace AnalyticCombinatorics.PartB.Ch6.ProcessOfSingularityAnalysis

/-- Three finite stages of the singularity analysis workflow. -/
structure SingularityAnalysisPipeline where
  located : Bool
  expanded : Bool
  transferred : Bool
deriving DecidableEq, Repr

def SingularityAnalysisPipeline.complete
    (p : SingularityAnalysisPipeline) : Bool :=
  p.located && p.expanded && p.transferred

theorem singularityAnalysisPipeline_complete_sample :
    ({ located := true, expanded := true,
       transferred := true } : SingularityAnalysisPipeline).complete =
      true := by
  native_decide

/-- Finite transfer budget accumulated after location and expansion. -/
def processTransferBudget (locate expand slack : ℕ) : ℕ :=
  locate + expand + slack

theorem processTransferBudget_sample :
    processTransferBudget 4 5 1 = 10 := by
  native_decide

structure SingularityProcessWindow where
  locateWindow : ℕ
  expandWindow : ℕ
  transferWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def SingularityProcessWindow.ready (w : SingularityProcessWindow) : Prop :=
  0 < w.locateWindow ∧
    w.transferWindow ≤ w.locateWindow + w.expandWindow + w.slack

def sampleSingularityProcessWindow : SingularityProcessWindow :=
  { locateWindow := 4, expandWindow := 5, transferWindow := 10, slack := 1 }

example : sampleSingularityProcessWindow.ready := by
  norm_num [SingularityProcessWindow.ready, sampleSingularityProcessWindow]

structure ProcessOfSingularityAnalysisBudgetCertificate where
  locateWindow : ℕ
  expandWindow : ℕ
  transferWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def ProcessOfSingularityAnalysisBudgetCertificate.controlled
    (c : ProcessOfSingularityAnalysisBudgetCertificate) : Prop :=
  0 < c.locateWindow ∧
    c.transferWindow ≤ c.locateWindow + c.expandWindow + c.slack

def ProcessOfSingularityAnalysisBudgetCertificate.budgetControlled
    (c : ProcessOfSingularityAnalysisBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.locateWindow + c.expandWindow + c.transferWindow + c.slack

def ProcessOfSingularityAnalysisBudgetCertificate.Ready
    (c : ProcessOfSingularityAnalysisBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def ProcessOfSingularityAnalysisBudgetCertificate.size
    (c : ProcessOfSingularityAnalysisBudgetCertificate) : ℕ :=
  c.locateWindow + c.expandWindow + c.transferWindow + c.slack

def sampleProcessOfSingularityAnalysisBudgetCertificate :
    ProcessOfSingularityAnalysisBudgetCertificate :=
  { locateWindow := 4
    expandWindow := 5
    transferWindow := 10
    certificateBudgetWindow := 20
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleProcessOfSingularityAnalysisBudgetCertificate.Ready := by
  constructor
  · norm_num [ProcessOfSingularityAnalysisBudgetCertificate.controlled,
      sampleProcessOfSingularityAnalysisBudgetCertificate]
  · norm_num [ProcessOfSingularityAnalysisBudgetCertificate.budgetControlled,
      sampleProcessOfSingularityAnalysisBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleProcessOfSingularityAnalysisBudgetCertificate.certificateBudgetWindow ≤
      sampleProcessOfSingularityAnalysisBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleProcessOfSingularityAnalysisBudgetCertificate.Ready := by
  constructor
  · norm_num [ProcessOfSingularityAnalysisBudgetCertificate.controlled,
      sampleProcessOfSingularityAnalysisBudgetCertificate]
  · norm_num [ProcessOfSingularityAnalysisBudgetCertificate.budgetControlled,
      sampleProcessOfSingularityAnalysisBudgetCertificate]

def budgetCertificateListReady
    (data : List ProcessOfSingularityAnalysisBudgetCertificate) : Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem sampleProcessOfSingularityAnalysisBudgetCertificate_ready :
    sampleProcessOfSingularityAnalysisBudgetCertificate.Ready := by
  constructor
  · norm_num [ProcessOfSingularityAnalysisBudgetCertificate.controlled,
      sampleProcessOfSingularityAnalysisBudgetCertificate]
  · norm_num [ProcessOfSingularityAnalysisBudgetCertificate.budgetControlled,
      sampleProcessOfSingularityAnalysisBudgetCertificate]

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleProcessOfSingularityAnalysisBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleProcessOfSingularityAnalysisBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch6.ProcessOfSingularityAnalysis
