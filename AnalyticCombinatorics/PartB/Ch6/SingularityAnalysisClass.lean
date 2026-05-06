import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Functions of singularity analysis class.

Finite closure-window bookkeeping for functions eligible for transfer
theorems.
-/

namespace AnalyticCombinatorics.PartB.Ch6.SingularityAnalysisClass

/-- Finite descriptor for a function in a singularity-analysis class. -/
structure SingularityClassDescriptor where
  analyticRadius : ℕ
  expansionOrder : ℕ
  hasTransferRule : Bool
deriving DecidableEq, Repr

def SingularityClassDescriptor.ready (d : SingularityClassDescriptor) : Prop :=
  0 < d.analyticRadius ∧ d.hasTransferRule = true

/-- Boolean readiness for executable finite audits. -/
def singularityClassDescriptorReadyBool (d : SingularityClassDescriptor) : Bool :=
  decide (0 < d.analyticRadius) && d.hasTransferRule

def sampleClassDescriptor : SingularityClassDescriptor :=
  { analyticRadius := 2, expansionOrder := 1, hasTransferRule := true }

theorem sampleClassDescriptor_ready :
    sampleClassDescriptor.ready ∧
      singularityClassDescriptorReadyBool sampleClassDescriptor = true := by
  constructor
  · norm_num [SingularityClassDescriptor.ready, sampleClassDescriptor]
  · unfold singularityClassDescriptorReadyBool sampleClassDescriptor
    native_decide

structure SingularityClassWindow where
  analyticWindow : ℕ
  singularExpansionWindow : ℕ
  closureWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def singularityClassReady (w : SingularityClassWindow) : Prop :=
  0 < w.analyticWindow ∧
    w.closureWindow ≤ w.analyticWindow + w.singularExpansionWindow + w.slack

def singularityClassBudget (w : SingularityClassWindow) : ℕ :=
  w.analyticWindow + w.singularExpansionWindow + w.closureWindow + w.slack

theorem closureWindow_le_singularityClassBudget
    (w : SingularityClassWindow) :
    w.closureWindow ≤ singularityClassBudget w := by
  unfold singularityClassBudget
  omega

def sampleSingularityClassWindow : SingularityClassWindow :=
  { analyticWindow := 5
    singularExpansionWindow := 4
    closureWindow := 8
    slack := 1 }

example : singularityClassReady sampleSingularityClassWindow := by
  norm_num [singularityClassReady, sampleSingularityClassWindow]

structure SingularityAnalysisClassBudgetCertificate where
  analyticWindow : ℕ
  expansionWindow : ℕ
  closureWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def SingularityAnalysisClassBudgetCertificate.controlled
    (c : SingularityAnalysisClassBudgetCertificate) : Prop :=
  0 < c.analyticWindow ∧
    c.closureWindow ≤ c.analyticWindow + c.expansionWindow + c.slack

def SingularityAnalysisClassBudgetCertificate.budgetControlled
    (c : SingularityAnalysisClassBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.analyticWindow + c.expansionWindow + c.closureWindow + c.slack

def SingularityAnalysisClassBudgetCertificate.Ready
    (c : SingularityAnalysisClassBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def SingularityAnalysisClassBudgetCertificate.size
    (c : SingularityAnalysisClassBudgetCertificate) : ℕ :=
  c.analyticWindow + c.expansionWindow + c.closureWindow + c.slack

theorem singularityAnalysisClass_budgetCertificate_le_size
    (c : SingularityAnalysisClassBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  exact h.2

def sampleSingularityAnalysisClassBudgetCertificate :
    SingularityAnalysisClassBudgetCertificate :=
  { analyticWindow := 5
    expansionWindow := 4
    closureWindow := 8
    certificateBudgetWindow := 18
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleSingularityAnalysisClassBudgetCertificate.Ready := by
  constructor
  · norm_num [SingularityAnalysisClassBudgetCertificate.controlled,
      sampleSingularityAnalysisClassBudgetCertificate]
  · norm_num [SingularityAnalysisClassBudgetCertificate.budgetControlled,
      sampleSingularityAnalysisClassBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleSingularityAnalysisClassBudgetCertificate.certificateBudgetWindow ≤
      sampleSingularityAnalysisClassBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleSingularityAnalysisClassBudgetCertificate.Ready := by
  constructor
  · norm_num [SingularityAnalysisClassBudgetCertificate.controlled,
      sampleSingularityAnalysisClassBudgetCertificate]
  · norm_num [SingularityAnalysisClassBudgetCertificate.budgetControlled,
      sampleSingularityAnalysisClassBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List SingularityAnalysisClassBudgetCertificate) : Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady [sampleSingularityAnalysisClassBudgetCertificate] = true := by
  unfold budgetCertificateListReady sampleSingularityAnalysisClassBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch6.SingularityAnalysisClass
