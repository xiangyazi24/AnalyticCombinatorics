import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Coefficient ratio schemas.

The finite data records numerator, denominator, and slack budgets for
coefficient-ratio estimates.
-/

namespace AnalyticCombinatorics.Asymptotics.CoefficientRatioSchemas

structure CoefficientRatioData where
  numeratorScale : ℕ
  denominatorScale : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def denominatorScalePositive (d : CoefficientRatioData) : Prop :=
  0 < d.denominatorScale

def numeratorControlled (d : CoefficientRatioData) : Prop :=
  d.numeratorScale ≤ d.denominatorScale + d.slack

def coefficientRatioReady (d : CoefficientRatioData) : Prop :=
  denominatorScalePositive d ∧ numeratorControlled d

def coefficientRatioBudget (d : CoefficientRatioData) : ℕ :=
  d.numeratorScale + d.denominatorScale + d.slack

theorem coefficientRatioReady.denominator {d : CoefficientRatioData}
    (h : coefficientRatioReady d) :
    denominatorScalePositive d ∧ numeratorControlled d ∧
      d.numeratorScale ≤ coefficientRatioBudget d := by
  refine ⟨h.1, h.2, ?_⟩
  unfold coefficientRatioBudget
  omega

theorem numeratorScale_le_ratioBudget (d : CoefficientRatioData) :
    d.numeratorScale ≤ coefficientRatioBudget d := by
  unfold coefficientRatioBudget
  omega

def sampleCoefficientRatioData : CoefficientRatioData :=
  { numeratorScale := 7, denominatorScale := 5, slack := 3 }

example : coefficientRatioReady sampleCoefficientRatioData := by
  norm_num [coefficientRatioReady, denominatorScalePositive]
  norm_num [numeratorControlled, sampleCoefficientRatioData]

example : coefficientRatioBudget sampleCoefficientRatioData = 15 := by
  native_decide

/-- Finite executable readiness audit for coefficient-ratio data. -/
def coefficientRatioDataListReady
    (data : List CoefficientRatioData) : Bool :=
  data.all fun d =>
    0 < d.denominatorScale && d.numeratorScale ≤ d.denominatorScale + d.slack

theorem coefficientRatioDataList_readyWindow :
    coefficientRatioDataListReady
      [{ numeratorScale := 4, denominatorScale := 3, slack := 1 },
       { numeratorScale := 7, denominatorScale := 5, slack := 3 }] = true := by
  unfold coefficientRatioDataListReady
  native_decide

/-- A bounded coefficient-ratio certificate window. -/
structure CoefficientRatioWindow where
  numeratorWindow : ℕ
  denominatorWindow : ℕ
  ratioSlack : ℕ
  ratioBudget : ℕ
  slack : ℕ

/-- The numerator window is controlled by the denominator window and slack. -/
def coefficientRatioWindowControlled (w : CoefficientRatioWindow) : Prop :=
  w.numeratorWindow ≤ w.denominatorWindow + w.ratioSlack + w.slack

/-- Readiness predicate for coefficient-ratio certificates. -/
def coefficientRatioWindowReady (w : CoefficientRatioWindow) : Prop :=
  0 < w.denominatorWindow ∧
    coefficientRatioWindowControlled w ∧
      w.ratioBudget ≤ w.numeratorWindow + w.denominatorWindow + w.slack

/-- Total size of the coefficient-ratio certificate window. -/
def coefficientRatioWindowCertificate (w : CoefficientRatioWindow) : ℕ :=
  w.numeratorWindow + w.denominatorWindow + w.ratioSlack + w.ratioBudget + w.slack

theorem coefficientRatioWindow_budget_le_certificate
    (w : CoefficientRatioWindow)
    (h : coefficientRatioWindowReady w) :
    w.ratioBudget ≤ coefficientRatioWindowCertificate w := by
  rcases h with ⟨_, _, hbudget⟩
  unfold coefficientRatioWindowCertificate
  omega

def sampleCoefficientRatioWindow : CoefficientRatioWindow where
  numeratorWindow := 9
  denominatorWindow := 6
  ratioSlack := 2
  ratioBudget := 14
  slack := 1

example :
    coefficientRatioWindowReady sampleCoefficientRatioWindow := by
  norm_num [coefficientRatioWindowReady,
    coefficientRatioWindowControlled, sampleCoefficientRatioWindow]

example :
    sampleCoefficientRatioWindow.ratioBudget ≤
      coefficientRatioWindowCertificate sampleCoefficientRatioWindow := by
  apply coefficientRatioWindow_budget_le_certificate
  norm_num [coefficientRatioWindowReady,
    coefficientRatioWindowControlled, sampleCoefficientRatioWindow]

structure CoefficientRatioRefinementCertificate where
  numeratorWindow : ℕ
  denominatorWindow : ℕ
  ratioSlackWindow : ℕ
  ratioBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def CoefficientRatioRefinementCertificate.numeratorControlled
    (c : CoefficientRatioRefinementCertificate) : Prop :=
  c.numeratorWindow ≤ c.denominatorWindow + c.ratioSlackWindow + c.slack

def CoefficientRatioRefinementCertificate.ratioBudgetControlled
    (c : CoefficientRatioRefinementCertificate) : Prop :=
  c.ratioBudgetWindow ≤
    c.numeratorWindow + c.denominatorWindow + c.ratioSlackWindow + c.slack

def coefficientRatioRefinementReady
    (c : CoefficientRatioRefinementCertificate) : Prop :=
  0 < c.denominatorWindow ∧
    c.numeratorControlled ∧
    c.ratioBudgetControlled

def CoefficientRatioRefinementCertificate.size
    (c : CoefficientRatioRefinementCertificate) : ℕ :=
  c.numeratorWindow + c.denominatorWindow + c.ratioSlackWindow + c.slack

theorem coefficientRatio_ratioBudgetWindow_le_size
    {c : CoefficientRatioRefinementCertificate}
    (h : coefficientRatioRefinementReady c) :
    c.ratioBudgetWindow ≤ c.size := by
  rcases h with ⟨_, _, hbudget⟩
  exact hbudget

def sampleCoefficientRatioRefinementCertificate :
    CoefficientRatioRefinementCertificate :=
  { numeratorWindow := 9, denominatorWindow := 6, ratioSlackWindow := 2,
    ratioBudgetWindow := 18, slack := 1 }

example : coefficientRatioRefinementReady
    sampleCoefficientRatioRefinementCertificate := by
  norm_num [coefficientRatioRefinementReady,
    CoefficientRatioRefinementCertificate.numeratorControlled,
    CoefficientRatioRefinementCertificate.ratioBudgetControlled,
    sampleCoefficientRatioRefinementCertificate]

example :
    sampleCoefficientRatioRefinementCertificate.ratioBudgetWindow ≤
      sampleCoefficientRatioRefinementCertificate.size := by
  norm_num [CoefficientRatioRefinementCertificate.size,
    sampleCoefficientRatioRefinementCertificate]

/-- A second-stage coefficient-ratio certificate with an external budget. -/
structure CoefficientRatioBudgetCertificate where
  numeratorWindow : ℕ
  denominatorWindow : ℕ
  ratioSlackWindow : ℕ
  ratioBudgetWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def CoefficientRatioBudgetCertificate.ratioControlled
    (cert : CoefficientRatioBudgetCertificate) : Prop :=
  0 < cert.denominatorWindow ∧
    cert.numeratorWindow ≤ cert.denominatorWindow + cert.ratioSlackWindow + cert.slack ∧
      cert.ratioBudgetWindow ≤
        cert.numeratorWindow + cert.denominatorWindow + cert.ratioSlackWindow + cert.slack

def CoefficientRatioBudgetCertificate.budgetControlled
    (cert : CoefficientRatioBudgetCertificate) : Prop :=
  cert.certificateBudgetWindow ≤
    cert.numeratorWindow + cert.denominatorWindow + cert.ratioSlackWindow +
      cert.ratioBudgetWindow + cert.slack

def coefficientRatioBudgetReady
    (cert : CoefficientRatioBudgetCertificate) : Prop :=
  cert.ratioControlled ∧ cert.budgetControlled

def CoefficientRatioBudgetCertificate.size
    (cert : CoefficientRatioBudgetCertificate) : ℕ :=
  cert.numeratorWindow + cert.denominatorWindow + cert.ratioSlackWindow +
    cert.ratioBudgetWindow + cert.slack

theorem coefficientRatio_certificateBudgetWindow_le_size
    (cert : CoefficientRatioBudgetCertificate)
    (h : coefficientRatioBudgetReady cert) :
    cert.certificateBudgetWindow ≤ cert.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleCoefficientRatioBudgetCertificate :
    CoefficientRatioBudgetCertificate :=
  { numeratorWindow := 9, denominatorWindow := 6, ratioSlackWindow := 2,
    ratioBudgetWindow := 18, certificateBudgetWindow := 36, slack := 1 }

example :
    coefficientRatioBudgetReady sampleCoefficientRatioBudgetCertificate := by
  norm_num [coefficientRatioBudgetReady,
    CoefficientRatioBudgetCertificate.ratioControlled,
    CoefficientRatioBudgetCertificate.budgetControlled,
    sampleCoefficientRatioBudgetCertificate]

example :
    sampleCoefficientRatioBudgetCertificate.certificateBudgetWindow ≤
      sampleCoefficientRatioBudgetCertificate.size := by
  apply coefficientRatio_certificateBudgetWindow_le_size
  norm_num [coefficientRatioBudgetReady,
    CoefficientRatioBudgetCertificate.ratioControlled,
    CoefficientRatioBudgetCertificate.budgetControlled,
    sampleCoefficientRatioBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    coefficientRatioBudgetReady sampleCoefficientRatioBudgetCertificate := by
  constructor
  · norm_num [CoefficientRatioBudgetCertificate.ratioControlled,
      sampleCoefficientRatioBudgetCertificate]
  · norm_num [CoefficientRatioBudgetCertificate.budgetControlled,
      sampleCoefficientRatioBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleCoefficientRatioBudgetCertificate.certificateBudgetWindow ≤
      sampleCoefficientRatioBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady
    (data : List CoefficientRatioBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleCoefficientRatioBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleCoefficientRatioBudgetCertificate
  native_decide
end AnalyticCombinatorics.Asymptotics.CoefficientRatioSchemas
