import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Regularly varying sequence schemas.

The finite model records an index budget and a comparison window for a
coefficient sequence.
-/

namespace AnalyticCombinatorics.AppC.RegularlyVaryingSequenceSchemas

structure RegularVariationWindow where
  indexBudget : ℕ
  comparisonStart : ℕ
  comparisonEnd : ℕ
deriving DecidableEq, Repr

def positiveIndexBudget (w : RegularVariationWindow) : Prop :=
  0 < w.indexBudget

def validComparisonWindow (w : RegularVariationWindow) : Prop :=
  w.comparisonStart ≤ w.comparisonEnd

def regularVariationWindowReady (w : RegularVariationWindow) : Prop :=
  positiveIndexBudget w ∧ validComparisonWindow w

def comparisonLength (w : RegularVariationWindow) : ℕ :=
  w.comparisonEnd - w.comparisonStart + 1

theorem regularVariationWindowReady.valid {w : RegularVariationWindow}
    (h : regularVariationWindowReady w) :
    validComparisonWindow w := by
  rcases h with ⟨hleft, hright⟩
  exact hright

theorem comparisonLength_positive (w : RegularVariationWindow) :
    0 < comparisonLength w := by
  unfold comparisonLength
  omega

def sampleRegularVariationWindow : RegularVariationWindow :=
  { indexBudget := 5, comparisonStart := 2, comparisonEnd := 6 }

example : regularVariationWindowReady sampleRegularVariationWindow := by
  norm_num
    [regularVariationWindowReady, positiveIndexBudget, validComparisonWindow,
      sampleRegularVariationWindow]

example : comparisonLength sampleRegularVariationWindow = 5 := by
  native_decide

structure RegularVariationCertificateWindow where
  indexWindow : ℕ
  comparisonStart : ℕ
  comparisonEnd : ℕ
  variationBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def RegularVariationCertificateWindow.windowValid
    (w : RegularVariationCertificateWindow) : Prop :=
  w.comparisonStart ≤ w.comparisonEnd + w.slack

def regularVariationCertificateReady (w : RegularVariationCertificateWindow) : Prop :=
  0 < w.indexWindow ∧ w.windowValid ∧
    w.variationBudget ≤ w.indexWindow + w.comparisonEnd + w.slack

def RegularVariationCertificateWindow.certificate
    (w : RegularVariationCertificateWindow) : ℕ :=
  w.indexWindow + w.comparisonStart + w.comparisonEnd + w.variationBudget + w.slack

theorem regularVariation_variationBudget_le_certificate
    (w : RegularVariationCertificateWindow) :
    w.variationBudget ≤ w.certificate := by
  unfold RegularVariationCertificateWindow.certificate
  omega

def sampleRegularVariationCertificateWindow : RegularVariationCertificateWindow :=
  { indexWindow := 5, comparisonStart := 2, comparisonEnd := 6,
    variationBudget := 12, slack := 1 }

example : regularVariationCertificateReady sampleRegularVariationCertificateWindow := by
  norm_num [regularVariationCertificateReady, RegularVariationCertificateWindow.windowValid,
    sampleRegularVariationCertificateWindow]


structure RegularlyVaryingSequenceSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def RegularlyVaryingSequenceSchemasBudgetCertificate.controlled
    (c : RegularlyVaryingSequenceSchemasBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def RegularlyVaryingSequenceSchemasBudgetCertificate.budgetControlled
    (c : RegularlyVaryingSequenceSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def RegularlyVaryingSequenceSchemasBudgetCertificate.Ready
    (c : RegularlyVaryingSequenceSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def RegularlyVaryingSequenceSchemasBudgetCertificate.size
    (c : RegularlyVaryingSequenceSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem regularlyVaryingSequenceSchemas_budgetCertificate_le_size
    (c : RegularlyVaryingSequenceSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleRegularlyVaryingSequenceSchemasBudgetCertificate :
    RegularlyVaryingSequenceSchemasBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleRegularlyVaryingSequenceSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [RegularlyVaryingSequenceSchemasBudgetCertificate.controlled,
      sampleRegularlyVaryingSequenceSchemasBudgetCertificate]
  · norm_num [RegularlyVaryingSequenceSchemasBudgetCertificate.budgetControlled,
      sampleRegularlyVaryingSequenceSchemasBudgetCertificate]

example : sampleRegularlyVaryingSequenceSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [RegularlyVaryingSequenceSchemasBudgetCertificate.controlled,
      sampleRegularlyVaryingSequenceSchemasBudgetCertificate]
  · norm_num [RegularlyVaryingSequenceSchemasBudgetCertificate.budgetControlled,
      sampleRegularlyVaryingSequenceSchemasBudgetCertificate]

example :
    sampleRegularlyVaryingSequenceSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleRegularlyVaryingSequenceSchemasBudgetCertificate.size := by
  apply regularlyVaryingSequenceSchemas_budgetCertificate_le_size
  constructor
  · norm_num [RegularlyVaryingSequenceSchemasBudgetCertificate.controlled,
      sampleRegularlyVaryingSequenceSchemasBudgetCertificate]
  · norm_num [RegularlyVaryingSequenceSchemasBudgetCertificate.budgetControlled,
      sampleRegularlyVaryingSequenceSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_le_size :
    sampleRegularlyVaryingSequenceSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleRegularlyVaryingSequenceSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady
    (data : List RegularlyVaryingSequenceSchemasBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleRegularlyVaryingSequenceSchemasBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleRegularlyVaryingSequenceSchemasBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppC.RegularlyVaryingSequenceSchemas
