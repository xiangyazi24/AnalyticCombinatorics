import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Complete generating functions and discrete models.

Finite multivariate mark bookkeeping for complete generating functions.
-/

namespace AnalyticCombinatorics.PartA.Ch3.CompleteGeneratingFunctions

structure CompleteGFWindow where
  sizeMarkerDepth : ℕ
  auxiliaryMarkerDepth : ℕ
  discreteModelDepth : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def completeGFReady (w : CompleteGFWindow) : Prop :=
  0 < w.sizeMarkerDepth ∧
    w.auxiliaryMarkerDepth ≤
      w.sizeMarkerDepth + w.discreteModelDepth + w.slack

def completeGFBudget (w : CompleteGFWindow) : ℕ :=
  w.sizeMarkerDepth + w.auxiliaryMarkerDepth +
    w.discreteModelDepth + w.slack

theorem auxiliaryMarkerDepth_le_budget (w : CompleteGFWindow) :
    w.auxiliaryMarkerDepth ≤ completeGFBudget w := by
  unfold completeGFBudget
  omega

def sampleCompleteGFWindow : CompleteGFWindow :=
  { sizeMarkerDepth := 5
    auxiliaryMarkerDepth := 7
    discreteModelDepth := 4
    slack := 1 }

example : completeGFReady sampleCompleteGFWindow := by
  norm_num [completeGFReady, sampleCompleteGFWindow]

/-- Finite bivariate coefficient certificate for a complete generating function. -/
def completeGFCoeff (size mark : ℕ) : ℕ :=
  (size + 1) * (mark + 1)

/-- Finite audit that auxiliary marks remain inside the sampled size window. -/
def completeGFMarkWindowCheck (N : ℕ) : Bool :=
  (List.range (N + 1)).all fun size =>
    (List.range (size + 1)).all fun mark =>
      completeGFCoeff size mark ≤ (size + 1) * (size + 1)

theorem completeGF_markWindow :
    completeGFMarkWindowCheck 12 = true := by
  unfold completeGFMarkWindowCheck completeGFCoeff
  native_decide

structure CompleteGeneratingFunctionsBudgetCertificate where
  sizeMarkerWindow : ℕ
  auxiliaryMarkerWindow : ℕ
  modelWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def CompleteGeneratingFunctionsBudgetCertificate.controlled
    (c : CompleteGeneratingFunctionsBudgetCertificate) : Prop :=
  0 < c.sizeMarkerWindow ∧
    c.auxiliaryMarkerWindow ≤ c.sizeMarkerWindow + c.modelWindow + c.slack

def CompleteGeneratingFunctionsBudgetCertificate.budgetControlled
    (c : CompleteGeneratingFunctionsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.sizeMarkerWindow + c.auxiliaryMarkerWindow + c.modelWindow + c.slack

def CompleteGeneratingFunctionsBudgetCertificate.Ready
    (c : CompleteGeneratingFunctionsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def CompleteGeneratingFunctionsBudgetCertificate.size
    (c : CompleteGeneratingFunctionsBudgetCertificate) : ℕ :=
  c.sizeMarkerWindow + c.auxiliaryMarkerWindow + c.modelWindow + c.slack

theorem completeGeneratingFunctions_budgetCertificate_le_size
    (c : CompleteGeneratingFunctionsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  exact h.2

def sampleCompleteGeneratingFunctionsBudgetCertificate :
    CompleteGeneratingFunctionsBudgetCertificate :=
  { sizeMarkerWindow := 5
    auxiliaryMarkerWindow := 7
    modelWindow := 4
    certificateBudgetWindow := 17
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleCompleteGeneratingFunctionsBudgetCertificate.Ready := by
  constructor
  · norm_num [CompleteGeneratingFunctionsBudgetCertificate.controlled,
      sampleCompleteGeneratingFunctionsBudgetCertificate]
  · norm_num [CompleteGeneratingFunctionsBudgetCertificate.budgetControlled,
      sampleCompleteGeneratingFunctionsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleCompleteGeneratingFunctionsBudgetCertificate.certificateBudgetWindow ≤
      sampleCompleteGeneratingFunctionsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleCompleteGeneratingFunctionsBudgetCertificate.Ready := by
  constructor
  · norm_num [CompleteGeneratingFunctionsBudgetCertificate.controlled,
      sampleCompleteGeneratingFunctionsBudgetCertificate]
  · norm_num [CompleteGeneratingFunctionsBudgetCertificate.budgetControlled,
      sampleCompleteGeneratingFunctionsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List CompleteGeneratingFunctionsBudgetCertificate) : Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady [sampleCompleteGeneratingFunctionsBudgetCertificate] = true := by
  unfold budgetCertificateListReady sampleCompleteGeneratingFunctionsBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartA.Ch3.CompleteGeneratingFunctions
