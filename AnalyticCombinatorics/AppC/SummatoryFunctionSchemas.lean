import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Summatory-function schema bookkeeping.

The definitions model finite prefix sums and domination of summatory
functions.
-/

namespace AnalyticCombinatorics.AppC.SummatoryFunctionSchemas

def prefixSum (a : ℕ → ℕ) (N : ℕ) : ℕ :=
  (List.range (N + 1)).map a |>.sum

def summatoryDominated (a b : ℕ → ℕ) (N : ℕ) : Prop :=
  prefixSum a N ≤ prefixSum b N

def constantSequence (c : ℕ) (n : ℕ) : ℕ := c + (n - n)

theorem prefixSum_zero (a : ℕ → ℕ) :
    prefixSum a 0 = a 0 := by
  simp [prefixSum]

theorem summatoryDominated_refl (a : ℕ → ℕ) (N : ℕ) :
    summatoryDominated a a N := by
  unfold summatoryDominated
  rfl

example : prefixSum (constantSequence 3) 4 = 15 := by
  native_decide

example : prefixSum (constantSequence 2) 3 ≤ prefixSum (constantSequence 5) 3 := by
  native_decide

structure SummatoryComparisonWindow where
  cutoff : ℕ
  lowerPrefix : ℕ
  upperPrefix : ℕ
  comparisonSlack : ℕ
deriving DecidableEq, Repr

def SummatoryComparisonWindow.ready (w : SummatoryComparisonWindow) : Prop :=
  w.lowerPrefix ≤ w.upperPrefix + w.comparisonSlack

def SummatoryComparisonWindow.gap (w : SummatoryComparisonWindow) : ℕ :=
  w.upperPrefix + w.comparisonSlack - w.lowerPrefix

def SummatoryComparisonWindow.certificate (w : SummatoryComparisonWindow) : ℕ :=
  w.cutoff + w.lowerPrefix + w.upperPrefix + w.comparisonSlack

theorem lowerPrefix_le_certificate (w : SummatoryComparisonWindow) :
    w.lowerPrefix ≤ w.certificate := by
  unfold SummatoryComparisonWindow.certificate
  omega

theorem upperPrefix_le_certificate (w : SummatoryComparisonWindow) :
    w.upperPrefix ≤ w.certificate := by
  unfold SummatoryComparisonWindow.certificate
  omega

def sampleSummatoryComparisonWindow : SummatoryComparisonWindow :=
  { cutoff := 5, lowerPrefix := 18, upperPrefix := 16, comparisonSlack := 4 }

example : sampleSummatoryComparisonWindow.ready := by
  norm_num [sampleSummatoryComparisonWindow, SummatoryComparisonWindow.ready]

example : sampleSummatoryComparisonWindow.gap = 2 := by
  norm_num [sampleSummatoryComparisonWindow, SummatoryComparisonWindow.gap]

structure SummatoryRefinementWindow where
  cutoffWindow : ℕ
  dominationWindow : ℕ
  errorWindow : ℕ
  summatoryBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def SummatoryRefinementWindow.dominationControlled
    (w : SummatoryRefinementWindow) : Prop :=
  w.dominationWindow ≤ w.cutoffWindow + w.errorWindow + w.slack

def summatoryRefinementWindowReady (w : SummatoryRefinementWindow) : Prop :=
  0 < w.cutoffWindow ∧ w.dominationControlled ∧
    w.summatoryBudget ≤ w.cutoffWindow + w.dominationWindow + w.errorWindow + w.slack

def SummatoryRefinementWindow.certificate (w : SummatoryRefinementWindow) : ℕ :=
  w.cutoffWindow + w.dominationWindow + w.errorWindow + w.summatoryBudget + w.slack

theorem summatoryRefinement_budget_le_certificate
    (w : SummatoryRefinementWindow) :
    w.summatoryBudget ≤ w.certificate := by
  unfold SummatoryRefinementWindow.certificate
  omega

def sampleSummatoryRefinementWindow : SummatoryRefinementWindow :=
  { cutoffWindow := 5, dominationWindow := 7, errorWindow := 2,
    summatoryBudget := 15, slack := 1 }

example : summatoryRefinementWindowReady sampleSummatoryRefinementWindow := by
  norm_num [summatoryRefinementWindowReady,
    SummatoryRefinementWindow.dominationControlled, sampleSummatoryRefinementWindow]


structure SummatoryFunctionSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def SummatoryFunctionSchemasBudgetCertificate.controlled
    (c : SummatoryFunctionSchemasBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def SummatoryFunctionSchemasBudgetCertificate.budgetControlled
    (c : SummatoryFunctionSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def SummatoryFunctionSchemasBudgetCertificate.Ready
    (c : SummatoryFunctionSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def SummatoryFunctionSchemasBudgetCertificate.size
    (c : SummatoryFunctionSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem summatoryFunctionSchemas_budgetCertificate_le_size
    (c : SummatoryFunctionSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleSummatoryFunctionSchemasBudgetCertificate :
    SummatoryFunctionSchemasBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

example : sampleSummatoryFunctionSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [SummatoryFunctionSchemasBudgetCertificate.controlled,
      sampleSummatoryFunctionSchemasBudgetCertificate]
  · norm_num [SummatoryFunctionSchemasBudgetCertificate.budgetControlled,
      sampleSummatoryFunctionSchemasBudgetCertificate]

example :
    sampleSummatoryFunctionSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleSummatoryFunctionSchemasBudgetCertificate.size := by
  apply summatoryFunctionSchemas_budgetCertificate_le_size
  constructor
  · norm_num [SummatoryFunctionSchemasBudgetCertificate.controlled,
      sampleSummatoryFunctionSchemasBudgetCertificate]
  · norm_num [SummatoryFunctionSchemasBudgetCertificate.budgetControlled,
      sampleSummatoryFunctionSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleSummatoryFunctionSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [SummatoryFunctionSchemasBudgetCertificate.controlled,
      sampleSummatoryFunctionSchemasBudgetCertificate]
  · norm_num [SummatoryFunctionSchemasBudgetCertificate.budgetControlled,
      sampleSummatoryFunctionSchemasBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleSummatoryFunctionSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleSummatoryFunctionSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List SummatoryFunctionSchemasBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleSummatoryFunctionSchemasBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleSummatoryFunctionSchemasBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppC.SummatoryFunctionSchemas
