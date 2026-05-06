import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Airy remainder window schemas.

This module records finite bookkeeping for Airy remainder windows.
-/

namespace AnalyticCombinatorics.PartB.Ch8.AiryRemainderWindowSchemas

structure AiryRemainderWindowData where
  airyScale : ℕ
  remainderWindow : ℕ
  transitionSlack : ℕ
deriving DecidableEq, Repr

def hasAiryScale (d : AiryRemainderWindowData) : Prop :=
  0 < d.airyScale

def remainderWindowControlled (d : AiryRemainderWindowData) : Prop :=
  d.remainderWindow ≤ d.airyScale + d.transitionSlack

def airyRemainderWindowReady (d : AiryRemainderWindowData) : Prop :=
  hasAiryScale d ∧ remainderWindowControlled d

def airyRemainderWindowBudget (d : AiryRemainderWindowData) : ℕ :=
  d.airyScale + d.remainderWindow + d.transitionSlack

theorem airyRemainderWindowReady.hasAiryScale
    {d : AiryRemainderWindowData}
    (h : airyRemainderWindowReady d) :
    hasAiryScale d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem remainderWindow_le_budget (d : AiryRemainderWindowData) :
    d.remainderWindow ≤ airyRemainderWindowBudget d := by
  unfold airyRemainderWindowBudget
  omega

def sampleAiryRemainderWindowData : AiryRemainderWindowData :=
  { airyScale := 6, remainderWindow := 8, transitionSlack := 3 }

example : airyRemainderWindowReady sampleAiryRemainderWindowData := by
  norm_num [airyRemainderWindowReady, hasAiryScale]
  norm_num [remainderWindowControlled, sampleAiryRemainderWindowData]

example : airyRemainderWindowBudget sampleAiryRemainderWindowData = 17 := by
  native_decide

structure AiryRemainderWindowBudgetCertificate where
  airyScaleWindow : ℕ
  remainderWindow : ℕ
  transitionSlackWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def AiryRemainderWindowBudgetCertificate.controlled
    (c : AiryRemainderWindowBudgetCertificate) : Prop :=
  0 < c.airyScaleWindow ∧
    c.remainderWindow ≤ c.airyScaleWindow + c.transitionSlackWindow + c.slack

def AiryRemainderWindowBudgetCertificate.budgetControlled
    (c : AiryRemainderWindowBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.airyScaleWindow + c.remainderWindow + c.transitionSlackWindow + c.slack

def AiryRemainderWindowBudgetCertificate.Ready
    (c : AiryRemainderWindowBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def AiryRemainderWindowBudgetCertificate.size
    (c : AiryRemainderWindowBudgetCertificate) : ℕ :=
  c.airyScaleWindow + c.remainderWindow + c.transitionSlackWindow + c.slack

theorem airyRemainderWindow_budgetCertificate_le_size
    (c : AiryRemainderWindowBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleAiryRemainderWindowBudgetCertificate :
    AiryRemainderWindowBudgetCertificate :=
  { airyScaleWindow := 6
    remainderWindow := 8
    transitionSlackWindow := 3
    certificateBudgetWindow := 18
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleAiryRemainderWindowBudgetCertificate.Ready := by
  constructor
  · norm_num [AiryRemainderWindowBudgetCertificate.controlled,
      sampleAiryRemainderWindowBudgetCertificate]
  · norm_num [AiryRemainderWindowBudgetCertificate.budgetControlled,
      sampleAiryRemainderWindowBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleAiryRemainderWindowBudgetCertificate.certificateBudgetWindow ≤
      sampleAiryRemainderWindowBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleAiryRemainderWindowBudgetCertificate.Ready := by
  constructor
  · norm_num [AiryRemainderWindowBudgetCertificate.controlled,
      sampleAiryRemainderWindowBudgetCertificate]
  · norm_num [AiryRemainderWindowBudgetCertificate.budgetControlled,
      sampleAiryRemainderWindowBudgetCertificate]

example :
    sampleAiryRemainderWindowBudgetCertificate.certificateBudgetWindow ≤
      sampleAiryRemainderWindowBudgetCertificate.size := by
  apply airyRemainderWindow_budgetCertificate_le_size
  constructor
  · norm_num [AiryRemainderWindowBudgetCertificate.controlled,
      sampleAiryRemainderWindowBudgetCertificate]
  · norm_num [AiryRemainderWindowBudgetCertificate.budgetControlled,
      sampleAiryRemainderWindowBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List AiryRemainderWindowBudgetCertificate) : Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady [sampleAiryRemainderWindowBudgetCertificate] = true := by
  unfold budgetCertificateListReady sampleAiryRemainderWindowBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch8.AiryRemainderWindowSchemas
