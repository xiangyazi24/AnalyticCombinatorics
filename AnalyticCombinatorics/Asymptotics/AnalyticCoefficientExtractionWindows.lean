import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Analytic coefficient extraction windows.

This module records finite bookkeeping for analytic coefficient extraction.
-/

namespace AnalyticCombinatorics.Asymptotics.AnalyticCoefficientExtractionWindows

structure CoefficientExtractionWindowData where
  coefficientScale : ℕ
  extractionWindow : ℕ
  analyticSlack : ℕ
deriving DecidableEq, Repr

def hasCoefficientScale
    (d : CoefficientExtractionWindowData) : Prop :=
  0 < d.coefficientScale

def extractionWindowControlled
    (d : CoefficientExtractionWindowData) : Prop :=
  d.extractionWindow ≤ d.coefficientScale + d.analyticSlack

def coefficientExtractionReady
    (d : CoefficientExtractionWindowData) : Prop :=
  hasCoefficientScale d ∧ extractionWindowControlled d

def coefficientExtractionBudget
    (d : CoefficientExtractionWindowData) : ℕ :=
  d.coefficientScale + d.extractionWindow + d.analyticSlack

theorem coefficientExtractionReady.hasCoefficientScale
    {d : CoefficientExtractionWindowData}
    (h : coefficientExtractionReady d) :
    hasCoefficientScale d ∧ extractionWindowControlled d ∧
      d.extractionWindow ≤ coefficientExtractionBudget d := by
  refine ⟨h.1, h.2, ?_⟩
  unfold coefficientExtractionBudget
  omega

theorem extractionWindow_le_budget
    (d : CoefficientExtractionWindowData) :
    d.extractionWindow ≤ coefficientExtractionBudget d := by
  unfold coefficientExtractionBudget
  omega

def sampleCoefficientExtractionWindowData :
    CoefficientExtractionWindowData :=
  { coefficientScale := 6, extractionWindow := 8, analyticSlack := 3 }

example : coefficientExtractionReady
    sampleCoefficientExtractionWindowData := by
  norm_num [coefficientExtractionReady, hasCoefficientScale]
  norm_num [extractionWindowControlled, sampleCoefficientExtractionWindowData]

example :
    coefficientExtractionBudget sampleCoefficientExtractionWindowData = 17 := by
  native_decide

/-- Finite executable readiness audit for coefficient extraction windows. -/
def coefficientExtractionListReady
    (windows : List CoefficientExtractionWindowData) : Bool :=
  windows.all fun d =>
    0 < d.coefficientScale &&
      d.extractionWindow ≤ d.coefficientScale + d.analyticSlack

theorem coefficientExtractionList_readyWindow :
    coefficientExtractionListReady
      [{ coefficientScale := 4, extractionWindow := 5, analyticSlack := 1 },
       { coefficientScale := 6, extractionWindow := 8, analyticSlack := 3 }] =
      true := by
  unfold coefficientExtractionListReady
  native_decide

/-- A certificate window for analytic coefficient extraction. -/
structure CoefficientExtractionCertificateWindow where
  coefficientWindow : ℕ
  extractionWindow : ℕ
  analyticSlack : ℕ
  certificateBudget : ℕ
  slack : ℕ

/-- The extraction window is controlled by the coefficient scale. -/
def coefficientExtractionCertificateControlled
    (w : CoefficientExtractionCertificateWindow) : Prop :=
  w.extractionWindow ≤ w.coefficientWindow + w.analyticSlack + w.slack

/-- Readiness for a coefficient extraction certificate. -/
def coefficientExtractionCertificateReady
    (w : CoefficientExtractionCertificateWindow) : Prop :=
  0 < w.coefficientWindow ∧
    coefficientExtractionCertificateControlled w ∧
      w.certificateBudget ≤ w.coefficientWindow + w.extractionWindow + w.slack

/-- Total size of a coefficient extraction certificate. -/
def coefficientExtractionCertificate
    (w : CoefficientExtractionCertificateWindow) : ℕ :=
  w.coefficientWindow + w.extractionWindow + w.analyticSlack +
    w.certificateBudget + w.slack

theorem coefficientExtractionCertificate_budget_le_certificate
    (w : CoefficientExtractionCertificateWindow)
    (h : coefficientExtractionCertificateReady w) :
    w.certificateBudget ≤ coefficientExtractionCertificate w := by
  rcases h with ⟨_, _, hbudget⟩
  unfold coefficientExtractionCertificate
  omega

def sampleCoefficientExtractionCertificateWindow :
    CoefficientExtractionCertificateWindow where
  coefficientWindow := 6
  extractionWindow := 7
  analyticSlack := 2
  certificateBudget := 12
  slack := 1

example :
    coefficientExtractionCertificateReady
      sampleCoefficientExtractionCertificateWindow := by
  norm_num [coefficientExtractionCertificateReady,
    coefficientExtractionCertificateControlled,
    sampleCoefficientExtractionCertificateWindow]

example :
    sampleCoefficientExtractionCertificateWindow.certificateBudget ≤
      coefficientExtractionCertificate
        sampleCoefficientExtractionCertificateWindow := by
  apply coefficientExtractionCertificate_budget_le_certificate
  norm_num [coefficientExtractionCertificateReady,
    coefficientExtractionCertificateControlled,
    sampleCoefficientExtractionCertificateWindow]

structure CoefficientExtractionRefinementCertificate where
  coefficientWindow : ℕ
  extractionWindow : ℕ
  analyticSlackWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def CoefficientExtractionRefinementCertificate.extractionControlled
    (c : CoefficientExtractionRefinementCertificate) : Prop :=
  c.extractionWindow ≤ c.coefficientWindow + c.analyticSlackWindow + c.slack

def CoefficientExtractionRefinementCertificate.certificateBudgetControlled
    (c : CoefficientExtractionRefinementCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.coefficientWindow + c.extractionWindow + c.analyticSlackWindow + c.slack

def coefficientExtractionRefinementReady
    (c : CoefficientExtractionRefinementCertificate) : Prop :=
  0 < c.coefficientWindow ∧ c.extractionControlled ∧ c.certificateBudgetControlled

def CoefficientExtractionRefinementCertificate.size
    (c : CoefficientExtractionRefinementCertificate) : ℕ :=
  c.coefficientWindow + c.extractionWindow + c.analyticSlackWindow + c.slack

theorem coefficientExtraction_certificateBudgetWindow_le_size
    {c : CoefficientExtractionRefinementCertificate}
    (h : coefficientExtractionRefinementReady c) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, _, hbudget⟩
  exact hbudget

def sampleCoefficientExtractionRefinementCertificate :
    CoefficientExtractionRefinementCertificate :=
  { coefficientWindow := 6, extractionWindow := 7, analyticSlackWindow := 2,
    certificateBudgetWindow := 16, slack := 1 }

example : coefficientExtractionRefinementReady
    sampleCoefficientExtractionRefinementCertificate := by
  norm_num [coefficientExtractionRefinementReady,
    CoefficientExtractionRefinementCertificate.extractionControlled,
    CoefficientExtractionRefinementCertificate.certificateBudgetControlled,
    sampleCoefficientExtractionRefinementCertificate]

example :
    sampleCoefficientExtractionRefinementCertificate.certificateBudgetWindow ≤
      sampleCoefficientExtractionRefinementCertificate.size := by
  norm_num [CoefficientExtractionRefinementCertificate.size,
    sampleCoefficientExtractionRefinementCertificate]

structure CoefficientExtractionBudgetCertificate where
  coefficientWindow : ℕ
  extractionWindow : ℕ
  analyticSlackWindow : ℕ
  extractionBudgetWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def CoefficientExtractionBudgetCertificate.controlled
    (c : CoefficientExtractionBudgetCertificate) : Prop :=
  0 < c.coefficientWindow ∧
    c.extractionWindow ≤ c.coefficientWindow + c.analyticSlackWindow + c.slack ∧
      c.extractionBudgetWindow ≤
        c.coefficientWindow + c.extractionWindow + c.analyticSlackWindow + c.slack

def CoefficientExtractionBudgetCertificate.budgetControlled
    (c : CoefficientExtractionBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.coefficientWindow + c.extractionWindow + c.analyticSlackWindow +
      c.extractionBudgetWindow + c.slack

def CoefficientExtractionBudgetCertificate.Ready
    (c : CoefficientExtractionBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def CoefficientExtractionBudgetCertificate.size
    (c : CoefficientExtractionBudgetCertificate) : ℕ :=
  c.coefficientWindow + c.extractionWindow + c.analyticSlackWindow +
    c.extractionBudgetWindow + c.slack

theorem coefficientExtraction_budgetCertificate_le_size
    (c : CoefficientExtractionBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleCoefficientExtractionBudgetCertificate :
    CoefficientExtractionBudgetCertificate :=
  { coefficientWindow := 6
    extractionWindow := 7
    analyticSlackWindow := 2
    extractionBudgetWindow := 16
    certificateBudgetWindow := 32
    slack := 1 }

example : sampleCoefficientExtractionBudgetCertificate.Ready := by
  constructor
  · norm_num [CoefficientExtractionBudgetCertificate.controlled,
      sampleCoefficientExtractionBudgetCertificate]
  · norm_num [CoefficientExtractionBudgetCertificate.budgetControlled,
      sampleCoefficientExtractionBudgetCertificate]

example :
    sampleCoefficientExtractionBudgetCertificate.certificateBudgetWindow ≤
      sampleCoefficientExtractionBudgetCertificate.size := by
  apply coefficientExtraction_budgetCertificate_le_size
  constructor
  · norm_num [CoefficientExtractionBudgetCertificate.controlled,
      sampleCoefficientExtractionBudgetCertificate]
  · norm_num [CoefficientExtractionBudgetCertificate.budgetControlled,
      sampleCoefficientExtractionBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleCoefficientExtractionBudgetCertificate.Ready := by
  constructor
  · norm_num [CoefficientExtractionBudgetCertificate.controlled,
      sampleCoefficientExtractionBudgetCertificate]
  · norm_num [CoefficientExtractionBudgetCertificate.budgetControlled,
      sampleCoefficientExtractionBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleCoefficientExtractionBudgetCertificate.certificateBudgetWindow ≤
      sampleCoefficientExtractionBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady
    (data : List CoefficientExtractionBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleCoefficientExtractionBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleCoefficientExtractionBudgetCertificate
  native_decide
end AnalyticCombinatorics.Asymptotics.AnalyticCoefficientExtractionWindows
