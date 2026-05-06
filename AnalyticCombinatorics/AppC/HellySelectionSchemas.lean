import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Helly selection schema bookkeeping.

The data records variation, boundedness, and subsequence extraction budgets.
-/

namespace AnalyticCombinatorics.AppC.HellySelectionSchemas

structure HellyData where
  variationBudget : ℕ
  boundedRange : ℕ
  extractionBudget : ℕ
deriving DecidableEq, Repr

def boundedVariation (d : HellyData) : Prop :=
  0 < d.variationBudget

def boundedRangePositive (d : HellyData) : Prop :=
  0 < d.boundedRange

def hellyReady (d : HellyData) : Prop :=
  boundedVariation d ∧ boundedRangePositive d

def hellyBudget (d : HellyData) : ℕ :=
  d.variationBudget + d.boundedRange + d.extractionBudget

theorem hellyReady.variation {d : HellyData}
    (h : hellyReady d) :
    boundedVariation d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem variationBudget_le_hellyBudget (d : HellyData) :
    d.variationBudget ≤ hellyBudget d := by
  unfold hellyBudget
  omega

def sampleHelly : HellyData :=
  { variationBudget := 4, boundedRange := 6, extractionBudget := 2 }

example : hellyReady sampleHelly := by
  norm_num [hellyReady, boundedVariation, boundedRangePositive, sampleHelly]

example : hellyBudget sampleHelly = 12 := by
  native_decide

structure HellyWindow where
  variationBudget : ℕ
  rangeBudget : ℕ
  extractedSubsequence : ℕ
  extractionSlack : ℕ
deriving DecidableEq, Repr

def HellyWindow.variationReady (w : HellyWindow) : Prop :=
  0 < w.variationBudget ∧ 0 < w.rangeBudget

def HellyWindow.extractionControlled (w : HellyWindow) : Prop :=
  w.extractedSubsequence ≤ w.variationBudget + w.rangeBudget + w.extractionSlack

def HellyWindow.ready (w : HellyWindow) : Prop :=
  w.variationReady ∧ w.extractionControlled

def HellyWindow.certificate (w : HellyWindow) : ℕ :=
  w.variationBudget + w.rangeBudget + w.extractedSubsequence + w.extractionSlack

theorem extractedSubsequence_le_certificate (w : HellyWindow) :
    w.extractedSubsequence ≤ w.certificate := by
  unfold HellyWindow.certificate
  omega

def sampleHellyWindow : HellyWindow :=
  { variationBudget := 4, rangeBudget := 6, extractedSubsequence := 5, extractionSlack := 0 }

example : sampleHellyWindow.ready := by
  norm_num [sampleHellyWindow, HellyWindow.ready, HellyWindow.variationReady,
    HellyWindow.extractionControlled]

structure HellyRefinementWindow where
  variationWindow : ℕ
  rangeWindow : ℕ
  extractionWindow : ℕ
  hellyBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def HellyRefinementWindow.extractionControlled
    (w : HellyRefinementWindow) : Prop :=
  w.extractionWindow ≤ w.variationWindow + w.rangeWindow + w.slack

def hellyRefinementWindowReady (w : HellyRefinementWindow) : Prop :=
  0 < w.variationWindow ∧ 0 < w.rangeWindow ∧ w.extractionControlled ∧
    w.hellyBudget ≤ w.variationWindow + w.rangeWindow + w.extractionWindow + w.slack

def HellyRefinementWindow.certificate (w : HellyRefinementWindow) : ℕ :=
  w.variationWindow + w.rangeWindow + w.extractionWindow + w.hellyBudget + w.slack

theorem hellyRefinement_budget_le_certificate
    (w : HellyRefinementWindow) :
    w.hellyBudget ≤ w.certificate := by
  unfold HellyRefinementWindow.certificate
  omega

def sampleHellyRefinementWindow : HellyRefinementWindow :=
  { variationWindow := 4, rangeWindow := 6, extractionWindow := 5,
    hellyBudget := 16, slack := 1 }

example : hellyRefinementWindowReady sampleHellyRefinementWindow := by
  norm_num [hellyRefinementWindowReady,
    HellyRefinementWindow.extractionControlled, sampleHellyRefinementWindow]


structure HellySelectionSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def HellySelectionSchemasBudgetCertificate.controlled
    (c : HellySelectionSchemasBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def HellySelectionSchemasBudgetCertificate.budgetControlled
    (c : HellySelectionSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def HellySelectionSchemasBudgetCertificate.Ready
    (c : HellySelectionSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def HellySelectionSchemasBudgetCertificate.size
    (c : HellySelectionSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem hellySelectionSchemas_budgetCertificate_le_size
    (c : HellySelectionSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleHellySelectionSchemasBudgetCertificate :
    HellySelectionSchemasBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

example : sampleHellySelectionSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [HellySelectionSchemasBudgetCertificate.controlled,
      sampleHellySelectionSchemasBudgetCertificate]
  · norm_num [HellySelectionSchemasBudgetCertificate.budgetControlled,
      sampleHellySelectionSchemasBudgetCertificate]

example :
    sampleHellySelectionSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleHellySelectionSchemasBudgetCertificate.size := by
  apply hellySelectionSchemas_budgetCertificate_le_size
  constructor
  · norm_num [HellySelectionSchemasBudgetCertificate.controlled,
      sampleHellySelectionSchemasBudgetCertificate]
  · norm_num [HellySelectionSchemasBudgetCertificate.budgetControlled,
      sampleHellySelectionSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleHellySelectionSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [HellySelectionSchemasBudgetCertificate.controlled,
      sampleHellySelectionSchemasBudgetCertificate]
  · norm_num [HellySelectionSchemasBudgetCertificate.budgetControlled,
      sampleHellySelectionSchemasBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleHellySelectionSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleHellySelectionSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List HellySelectionSchemasBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleHellySelectionSchemasBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleHellySelectionSchemasBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppC.HellySelectionSchemas
