import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Polynomial scale schema bookkeeping.

The module records degree, leading coefficient, and error budgets for
polynomial growth scales.
-/

namespace AnalyticCombinatorics.Asymptotics.PolynomialScaleSchemas

structure PolynomialScaleData where
  degree : ℕ
  leadingBudget : ℕ
  errorBudget : ℕ
deriving DecidableEq, Repr

def positiveDegree (d : PolynomialScaleData) : Prop :=
  0 < d.degree

def positiveLeadingBudget (d : PolynomialScaleData) : Prop :=
  0 < d.leadingBudget

def polynomialScaleReady (d : PolynomialScaleData) : Prop :=
  positiveDegree d ∧ positiveLeadingBudget d

def polynomialScaleBudget (d : PolynomialScaleData) : ℕ :=
  d.degree * d.leadingBudget + d.errorBudget

theorem polynomialScaleReady.leading {d : PolynomialScaleData}
    (h : polynomialScaleReady d) :
    positiveDegree d ∧ positiveLeadingBudget d ∧ d.errorBudget ≤ polynomialScaleBudget d := by
  refine ⟨h.1, h.2, ?_⟩
  unfold polynomialScaleBudget
  omega

theorem errorBudget_le_polynomialScaleBudget (d : PolynomialScaleData) :
    d.errorBudget ≤ polynomialScaleBudget d := by
  unfold polynomialScaleBudget
  omega

def samplePolynomialScale : PolynomialScaleData :=
  { degree := 3, leadingBudget := 4, errorBudget := 2 }

example : polynomialScaleReady samplePolynomialScale := by
  norm_num [polynomialScaleReady, positiveDegree, positiveLeadingBudget, samplePolynomialScale]

example : polynomialScaleBudget samplePolynomialScale = 14 := by
  native_decide

/-- Finite executable readiness audit for polynomial scale data. -/
def polynomialScaleDataListReady
    (data : List PolynomialScaleData) : Bool :=
  data.all fun d => 0 < d.degree && 0 < d.leadingBudget

theorem polynomialScaleDataList_readyWindow :
    polynomialScaleDataListReady
      [{ degree := 2, leadingBudget := 3, errorBudget := 1 },
       { degree := 3, leadingBudget := 4, errorBudget := 2 }] = true := by
  unfold polynomialScaleDataListReady
  native_decide

structure PolynomialScaleWindow where
  degree : ℕ
  leadingBudget : ℕ
  errorBudget : ℕ
  coefficientBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def PolynomialScaleWindow.errorControlled (w : PolynomialScaleWindow) : Prop :=
  w.errorBudget ≤ w.degree * w.leadingBudget + w.slack

def PolynomialScaleWindow.coefficientControlled (w : PolynomialScaleWindow) : Prop :=
  w.coefficientBudget ≤ w.degree * w.leadingBudget + w.errorBudget + w.slack

def polynomialScaleWindowReady (w : PolynomialScaleWindow) : Prop :=
  0 < w.degree ∧
    0 < w.leadingBudget ∧
    w.errorControlled ∧
    w.coefficientControlled

def PolynomialScaleWindow.certificate (w : PolynomialScaleWindow) : ℕ :=
  w.degree * w.leadingBudget + w.errorBudget + w.slack

theorem polynomialScale_coefficientBudget_le_certificate {w : PolynomialScaleWindow}
    (h : polynomialScaleWindowReady w) :
    w.coefficientBudget ≤ w.certificate := by
  rcases h with ⟨_, _, _, hcoeff⟩
  exact hcoeff

def samplePolynomialScaleWindow : PolynomialScaleWindow :=
  { degree := 3, leadingBudget := 4, errorBudget := 2, coefficientBudget := 13, slack := 0 }

example : polynomialScaleWindowReady samplePolynomialScaleWindow := by
  norm_num [polynomialScaleWindowReady, PolynomialScaleWindow.errorControlled,
    PolynomialScaleWindow.coefficientControlled, samplePolynomialScaleWindow]

example : samplePolynomialScaleWindow.certificate = 14 := by
  native_decide

structure PolynomialScaleCertificate where
  degreeWindow : ℕ
  leadingWindow : ℕ
  errorWindow : ℕ
  coefficientWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def PolynomialScaleCertificate.errorControlled
    (c : PolynomialScaleCertificate) : Prop :=
  c.errorWindow ≤ c.degreeWindow * c.leadingWindow + c.slack

def PolynomialScaleCertificate.coefficientControlled
    (c : PolynomialScaleCertificate) : Prop :=
  c.coefficientWindow ≤ c.degreeWindow * c.leadingWindow + c.errorWindow + c.slack

def polynomialScaleCertificateReady
    (c : PolynomialScaleCertificate) : Prop :=
  0 < c.degreeWindow ∧
    0 < c.leadingWindow ∧
    c.errorControlled ∧
    c.coefficientControlled

def PolynomialScaleCertificate.size
    (c : PolynomialScaleCertificate) : ℕ :=
  c.degreeWindow * c.leadingWindow + c.errorWindow + c.slack

theorem polynomialScale_coefficientWindow_le_size
    {c : PolynomialScaleCertificate}
    (h : polynomialScaleCertificateReady c) :
    c.coefficientWindow ≤ c.size := by
  rcases h with ⟨_, _, _, hcoefficient⟩
  exact hcoefficient

def samplePolynomialScaleCertificate : PolynomialScaleCertificate :=
  { degreeWindow := 3, leadingWindow := 4, errorWindow := 2,
    coefficientWindow := 13, slack := 0 }

example : polynomialScaleCertificateReady samplePolynomialScaleCertificate := by
  norm_num [polynomialScaleCertificateReady,
    PolynomialScaleCertificate.errorControlled,
    PolynomialScaleCertificate.coefficientControlled,
    samplePolynomialScaleCertificate]

example :
    samplePolynomialScaleCertificate.coefficientWindow ≤
      samplePolynomialScaleCertificate.size := by
  norm_num [PolynomialScaleCertificate.size, samplePolynomialScaleCertificate]

/-- A refinement certificate with the polynomial coefficient budget separated from size. -/
structure PolynomialScaleRefinementCertificate where
  degreeWindow : ℕ
  leadingWindow : ℕ
  errorWindow : ℕ
  coefficientWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def PolynomialScaleRefinementCertificate.scaleControlled
    (cert : PolynomialScaleRefinementCertificate) : Prop :=
  0 < cert.degreeWindow ∧
    0 < cert.leadingWindow ∧
      cert.errorWindow ≤ cert.degreeWindow * cert.leadingWindow + cert.slack ∧
        cert.coefficientWindow ≤
          cert.degreeWindow * cert.leadingWindow + cert.errorWindow + cert.slack

def PolynomialScaleRefinementCertificate.budgetControlled
    (cert : PolynomialScaleRefinementCertificate) : Prop :=
  cert.certificateBudgetWindow ≤
    cert.degreeWindow * cert.leadingWindow + cert.errorWindow + cert.slack

def polynomialScaleRefinementReady
    (cert : PolynomialScaleRefinementCertificate) : Prop :=
  cert.scaleControlled ∧ cert.budgetControlled

def PolynomialScaleRefinementCertificate.size
    (cert : PolynomialScaleRefinementCertificate) : ℕ :=
  cert.degreeWindow * cert.leadingWindow + cert.errorWindow + cert.slack

theorem polynomialScale_certificateBudgetWindow_le_size
    (cert : PolynomialScaleRefinementCertificate)
    (h : polynomialScaleRefinementReady cert) :
    cert.certificateBudgetWindow ≤ cert.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def samplePolynomialScaleRefinementCertificate :
    PolynomialScaleRefinementCertificate :=
  { degreeWindow := 3, leadingWindow := 4, errorWindow := 2,
    coefficientWindow := 13, certificateBudgetWindow := 14, slack := 0 }

example :
    polynomialScaleRefinementReady samplePolynomialScaleRefinementCertificate := by
  norm_num [polynomialScaleRefinementReady,
    PolynomialScaleRefinementCertificate.scaleControlled,
    PolynomialScaleRefinementCertificate.budgetControlled,
    samplePolynomialScaleRefinementCertificate]

example :
    samplePolynomialScaleRefinementCertificate.certificateBudgetWindow ≤
      samplePolynomialScaleRefinementCertificate.size := by
  apply polynomialScale_certificateBudgetWindow_le_size
  norm_num [polynomialScaleRefinementReady,
    PolynomialScaleRefinementCertificate.scaleControlled,
    PolynomialScaleRefinementCertificate.budgetControlled,
    samplePolynomialScaleRefinementCertificate]


structure PolynomialScaleSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def PolynomialScaleSchemasBudgetCertificate.controlled
    (c : PolynomialScaleSchemasBudgetCertificate) : Prop :=
  0 < c.primaryWindow ∧ c.secondaryWindow ≤ c.primaryWindow + c.slack

def PolynomialScaleSchemasBudgetCertificate.budgetControlled
    (c : PolynomialScaleSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def PolynomialScaleSchemasBudgetCertificate.Ready
    (c : PolynomialScaleSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def PolynomialScaleSchemasBudgetCertificate.size
    (c : PolynomialScaleSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem polynomialScaleSchemas_budgetCertificate_le_size
    (c : PolynomialScaleSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def samplePolynomialScaleSchemasBudgetCertificate :
    PolynomialScaleSchemasBudgetCertificate :=
  { primaryWindow := 5
    secondaryWindow := 6
    certificateBudgetWindow := 12
    slack := 1 }

example : samplePolynomialScaleSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [PolynomialScaleSchemasBudgetCertificate.controlled,
      samplePolynomialScaleSchemasBudgetCertificate]
  · norm_num [PolynomialScaleSchemasBudgetCertificate.budgetControlled,
      samplePolynomialScaleSchemasBudgetCertificate]

example :
    samplePolynomialScaleSchemasBudgetCertificate.certificateBudgetWindow ≤
      samplePolynomialScaleSchemasBudgetCertificate.size := by
  apply polynomialScaleSchemas_budgetCertificate_le_size
  constructor
  · norm_num [PolynomialScaleSchemasBudgetCertificate.controlled,
      samplePolynomialScaleSchemasBudgetCertificate]
  · norm_num [PolynomialScaleSchemasBudgetCertificate.budgetControlled,
      samplePolynomialScaleSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    samplePolynomialScaleSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [PolynomialScaleSchemasBudgetCertificate.controlled,
      samplePolynomialScaleSchemasBudgetCertificate]
  · norm_num [PolynomialScaleSchemasBudgetCertificate.budgetControlled,
      samplePolynomialScaleSchemasBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    samplePolynomialScaleSchemasBudgetCertificate.certificateBudgetWindow ≤
      samplePolynomialScaleSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady
    (data : List PolynomialScaleSchemasBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [samplePolynomialScaleSchemasBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    samplePolynomialScaleSchemasBudgetCertificate
  native_decide
end AnalyticCombinatorics.Asymptotics.PolynomialScaleSchemas
