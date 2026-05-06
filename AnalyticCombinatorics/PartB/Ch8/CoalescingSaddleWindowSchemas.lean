import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Coalescing saddle window schemas.

The finite schema records saddle gap, local scale, and Airy slack.
-/

namespace AnalyticCombinatorics.PartB.Ch8.CoalescingSaddleWindowSchemas

structure CoalescingSaddleWindowData where
  saddleGap : ℕ
  localScale : ℕ
  airySlack : ℕ
deriving DecidableEq, Repr

def saddleGapPositive (d : CoalescingSaddleWindowData) : Prop :=
  0 < d.saddleGap

def localScaleControlled (d : CoalescingSaddleWindowData) : Prop :=
  d.localScale ≤ d.saddleGap + d.airySlack

def coalescingSaddleWindowReady
    (d : CoalescingSaddleWindowData) : Prop :=
  saddleGapPositive d ∧ localScaleControlled d

def coalescingSaddleWindowBudget
    (d : CoalescingSaddleWindowData) : ℕ :=
  d.saddleGap + d.localScale + d.airySlack

theorem coalescingSaddleWindowReady.gap
    {d : CoalescingSaddleWindowData}
    (h : coalescingSaddleWindowReady d) :
    saddleGapPositive d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem localScale_le_coalescingSaddleBudget
    (d : CoalescingSaddleWindowData) :
    d.localScale ≤ coalescingSaddleWindowBudget d := by
  unfold coalescingSaddleWindowBudget
  omega

def sampleCoalescingSaddleWindowData : CoalescingSaddleWindowData :=
  { saddleGap := 5, localScale := 7, airySlack := 3 }

example :
    coalescingSaddleWindowReady sampleCoalescingSaddleWindowData := by
  norm_num [coalescingSaddleWindowReady, saddleGapPositive]
  norm_num [localScaleControlled, sampleCoalescingSaddleWindowData]

example :
    coalescingSaddleWindowBudget sampleCoalescingSaddleWindowData = 15 := by
  native_decide


structure CoalescingSaddleWindowSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def CoalescingSaddleWindowSchemasBudgetCertificate.controlled
    (c : CoalescingSaddleWindowSchemasBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def CoalescingSaddleWindowSchemasBudgetCertificate.budgetControlled
    (c : CoalescingSaddleWindowSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def CoalescingSaddleWindowSchemasBudgetCertificate.Ready
    (c : CoalescingSaddleWindowSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def CoalescingSaddleWindowSchemasBudgetCertificate.size
    (c : CoalescingSaddleWindowSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem coalescingSaddleWindowSchemas_budgetCertificate_le_size
    (c : CoalescingSaddleWindowSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleCoalescingSaddleWindowSchemasBudgetCertificate :
    CoalescingSaddleWindowSchemasBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleCoalescingSaddleWindowSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [CoalescingSaddleWindowSchemasBudgetCertificate.controlled,
      sampleCoalescingSaddleWindowSchemasBudgetCertificate]
  · norm_num [CoalescingSaddleWindowSchemasBudgetCertificate.budgetControlled,
      sampleCoalescingSaddleWindowSchemasBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleCoalescingSaddleWindowSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleCoalescingSaddleWindowSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleCoalescingSaddleWindowSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [CoalescingSaddleWindowSchemasBudgetCertificate.controlled,
      sampleCoalescingSaddleWindowSchemasBudgetCertificate]
  · norm_num [CoalescingSaddleWindowSchemasBudgetCertificate.budgetControlled,
      sampleCoalescingSaddleWindowSchemasBudgetCertificate]

example :
    sampleCoalescingSaddleWindowSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleCoalescingSaddleWindowSchemasBudgetCertificate.size := by
  apply coalescingSaddleWindowSchemas_budgetCertificate_le_size
  constructor
  · norm_num [CoalescingSaddleWindowSchemasBudgetCertificate.controlled,
      sampleCoalescingSaddleWindowSchemasBudgetCertificate]
  · norm_num [CoalescingSaddleWindowSchemasBudgetCertificate.budgetControlled,
      sampleCoalescingSaddleWindowSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady
    (data : List CoalescingSaddleWindowSchemasBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleCoalescingSaddleWindowSchemasBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleCoalescingSaddleWindowSchemasBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch8.CoalescingSaddleWindowSchemas
