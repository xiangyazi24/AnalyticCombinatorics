import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Coalescing Airy window schemas.

This module records finite bookkeeping for coalescing Airy saddle windows.
-/

namespace AnalyticCombinatorics.PartB.Ch8.CoalescingAiryWindowSchemas

structure CoalescingAiryWindowData where
  coalescenceOrder : ℕ
  airyScale : ℕ
  saddleSlack : ℕ
deriving DecidableEq, Repr

def hasCoalescenceOrder (d : CoalescingAiryWindowData) : Prop :=
  0 < d.coalescenceOrder

def airyScaleControlled (d : CoalescingAiryWindowData) : Prop :=
  d.airyScale ≤ d.coalescenceOrder + d.saddleSlack

def coalescingAiryReady (d : CoalescingAiryWindowData) : Prop :=
  hasCoalescenceOrder d ∧ airyScaleControlled d

def coalescingAiryBudget (d : CoalescingAiryWindowData) : ℕ :=
  d.coalescenceOrder + d.airyScale + d.saddleSlack

theorem coalescingAiryReady.hasCoalescenceOrder
    {d : CoalescingAiryWindowData}
    (h : coalescingAiryReady d) :
    hasCoalescenceOrder d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem airyScale_le_budget (d : CoalescingAiryWindowData) :
    d.airyScale ≤ coalescingAiryBudget d := by
  unfold coalescingAiryBudget
  omega

def sampleCoalescingAiryWindowData : CoalescingAiryWindowData :=
  { coalescenceOrder := 7, airyScale := 9, saddleSlack := 3 }

example : coalescingAiryReady sampleCoalescingAiryWindowData := by
  norm_num [coalescingAiryReady, hasCoalescenceOrder]
  norm_num [airyScaleControlled, sampleCoalescingAiryWindowData]

example : coalescingAiryBudget sampleCoalescingAiryWindowData = 19 := by
  native_decide

/-- Finite executable readiness audit for coalescing Airy windows. -/
def coalescingAiryListReady
    (windows : List CoalescingAiryWindowData) : Bool :=
  windows.all fun d =>
    0 < d.coalescenceOrder && d.airyScale ≤ d.coalescenceOrder + d.saddleSlack

theorem coalescingAiryList_readyWindow :
    coalescingAiryListReady
      [{ coalescenceOrder := 4, airyScale := 5, saddleSlack := 1 },
       { coalescenceOrder := 7, airyScale := 9, saddleSlack := 3 }] = true := by
  unfold coalescingAiryListReady
  native_decide

structure CoalescingAiryWindowBudgetCertificate where
  coalescenceOrderWindow : ℕ
  airyScaleWindow : ℕ
  saddleSlackWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def CoalescingAiryWindowBudgetCertificate.controlled
    (c : CoalescingAiryWindowBudgetCertificate) : Prop :=
  0 < c.coalescenceOrderWindow ∧
    c.airyScaleWindow ≤ c.coalescenceOrderWindow + c.saddleSlackWindow + c.slack

def CoalescingAiryWindowBudgetCertificate.budgetControlled
    (c : CoalescingAiryWindowBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.coalescenceOrderWindow + c.airyScaleWindow + c.saddleSlackWindow + c.slack

def CoalescingAiryWindowBudgetCertificate.Ready
    (c : CoalescingAiryWindowBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def CoalescingAiryWindowBudgetCertificate.size
    (c : CoalescingAiryWindowBudgetCertificate) : ℕ :=
  c.coalescenceOrderWindow + c.airyScaleWindow + c.saddleSlackWindow + c.slack

theorem coalescingAiryWindow_budgetCertificate_le_size
    (c : CoalescingAiryWindowBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleCoalescingAiryWindowBudgetCertificate :
    CoalescingAiryWindowBudgetCertificate :=
  { coalescenceOrderWindow := 7
    airyScaleWindow := 9
    saddleSlackWindow := 3
    certificateBudgetWindow := 20
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleCoalescingAiryWindowBudgetCertificate.Ready := by
  constructor
  · norm_num [CoalescingAiryWindowBudgetCertificate.controlled,
      sampleCoalescingAiryWindowBudgetCertificate]
  · norm_num [CoalescingAiryWindowBudgetCertificate.budgetControlled,
      sampleCoalescingAiryWindowBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleCoalescingAiryWindowBudgetCertificate.certificateBudgetWindow ≤
      sampleCoalescingAiryWindowBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleCoalescingAiryWindowBudgetCertificate.Ready := by
  constructor
  · norm_num [CoalescingAiryWindowBudgetCertificate.controlled,
      sampleCoalescingAiryWindowBudgetCertificate]
  · norm_num [CoalescingAiryWindowBudgetCertificate.budgetControlled,
      sampleCoalescingAiryWindowBudgetCertificate]

example :
    sampleCoalescingAiryWindowBudgetCertificate.certificateBudgetWindow ≤
      sampleCoalescingAiryWindowBudgetCertificate.size := by
  apply coalescingAiryWindow_budgetCertificate_le_size
  constructor
  · norm_num [CoalescingAiryWindowBudgetCertificate.controlled,
      sampleCoalescingAiryWindowBudgetCertificate]
  · norm_num [CoalescingAiryWindowBudgetCertificate.budgetControlled,
      sampleCoalescingAiryWindowBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady
    (data : List CoalescingAiryWindowBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleCoalescingAiryWindowBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleCoalescingAiryWindowBudgetCertificate
  native_decide
end AnalyticCombinatorics.PartB.Ch8.CoalescingAiryWindowSchemas
