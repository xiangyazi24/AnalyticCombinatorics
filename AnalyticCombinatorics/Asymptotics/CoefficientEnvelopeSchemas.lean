import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Coefficient envelope schemas.

The finite record stores envelope height, coefficient window, and error
slack.
-/

namespace AnalyticCombinatorics.Asymptotics.CoefficientEnvelopeSchemas

structure CoefficientEnvelopeData where
  envelopeHeight : ℕ
  coefficientWindow : ℕ
  errorSlack : ℕ
deriving DecidableEq, Repr

def envelopeHeightPositive (d : CoefficientEnvelopeData) : Prop :=
  0 < d.envelopeHeight

def coefficientWindowControlled (d : CoefficientEnvelopeData) : Prop :=
  d.coefficientWindow ≤ d.envelopeHeight + d.errorSlack

def coefficientEnvelopeReady (d : CoefficientEnvelopeData) : Prop :=
  envelopeHeightPositive d ∧ coefficientWindowControlled d

def coefficientEnvelopeBudget (d : CoefficientEnvelopeData) : ℕ :=
  d.envelopeHeight + d.coefficientWindow + d.errorSlack

theorem coefficientEnvelopeReady.height {d : CoefficientEnvelopeData}
    (h : coefficientEnvelopeReady d) :
    envelopeHeightPositive d ∧ coefficientWindowControlled d ∧
      d.coefficientWindow ≤ coefficientEnvelopeBudget d := by
  refine ⟨h.1, h.2, ?_⟩
  unfold coefficientEnvelopeBudget
  omega

theorem coefficientWindow_le_envelopeBudget (d : CoefficientEnvelopeData) :
    d.coefficientWindow ≤ coefficientEnvelopeBudget d := by
  unfold coefficientEnvelopeBudget
  omega

def sampleCoefficientEnvelopeData : CoefficientEnvelopeData :=
  { envelopeHeight := 6, coefficientWindow := 8, errorSlack := 3 }

example : coefficientEnvelopeReady sampleCoefficientEnvelopeData := by
  norm_num [coefficientEnvelopeReady, envelopeHeightPositive]
  norm_num [coefficientWindowControlled, sampleCoefficientEnvelopeData]

example : coefficientEnvelopeBudget sampleCoefficientEnvelopeData = 17 := by
  native_decide

/-- Finite executable readiness audit for coefficient envelope data. -/
def coefficientEnvelopeDataListReady
    (data : List CoefficientEnvelopeData) : Bool :=
  data.all fun d =>
    0 < d.envelopeHeight &&
      d.coefficientWindow ≤ d.envelopeHeight + d.errorSlack

theorem coefficientEnvelopeDataList_readyWindow :
    coefficientEnvelopeDataListReady
      [{ envelopeHeight := 4, coefficientWindow := 5, errorSlack := 1 },
       { envelopeHeight := 6, coefficientWindow := 8, errorSlack := 3 }] = true := by
  unfold coefficientEnvelopeDataListReady
  native_decide

/-- A bounded coefficient envelope window. -/
structure CoefficientEnvelopeWindow where
  envelopeWindow : ℕ
  coefficientWindow : ℕ
  errorSlack : ℕ
  envelopeBudget : ℕ
  slack : ℕ

/-- The coefficient window is controlled by the envelope window. -/
def coefficientEnvelopeWindowControlled (w : CoefficientEnvelopeWindow) : Prop :=
  w.coefficientWindow ≤ w.envelopeWindow + w.errorSlack + w.slack

/-- Readiness predicate for a bounded coefficient envelope window. -/
def coefficientEnvelopeWindowReady (w : CoefficientEnvelopeWindow) : Prop :=
  0 < w.envelopeWindow ∧
    coefficientEnvelopeWindowControlled w ∧
      w.envelopeBudget ≤ w.envelopeWindow + w.coefficientWindow + w.slack

/-- Total certificate size for the envelope window. -/
def coefficientEnvelopeWindowCertificate (w : CoefficientEnvelopeWindow) : ℕ :=
  w.envelopeWindow + w.coefficientWindow + w.errorSlack + w.envelopeBudget + w.slack

theorem coefficientEnvelopeWindow_budget_le_certificate
    (w : CoefficientEnvelopeWindow)
    (h : coefficientEnvelopeWindowReady w) :
    w.envelopeBudget ≤ coefficientEnvelopeWindowCertificate w := by
  rcases h with ⟨_, _, hbudget⟩
  unfold coefficientEnvelopeWindowCertificate
  omega

def sampleCoefficientEnvelopeWindow : CoefficientEnvelopeWindow where
  envelopeWindow := 6
  coefficientWindow := 7
  errorSlack := 2
  envelopeBudget := 12
  slack := 1

example :
    coefficientEnvelopeWindowReady sampleCoefficientEnvelopeWindow := by
  norm_num [coefficientEnvelopeWindowReady,
    coefficientEnvelopeWindowControlled, sampleCoefficientEnvelopeWindow]

example :
    sampleCoefficientEnvelopeWindow.envelopeBudget ≤
      coefficientEnvelopeWindowCertificate sampleCoefficientEnvelopeWindow := by
  apply coefficientEnvelopeWindow_budget_le_certificate
  norm_num [coefficientEnvelopeWindowReady,
    coefficientEnvelopeWindowControlled, sampleCoefficientEnvelopeWindow]

structure CoefficientEnvelopeRefinementCertificate where
  envelopeWindow : ℕ
  coefficientWindow : ℕ
  errorSlackWindow : ℕ
  envelopeBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def CoefficientEnvelopeRefinementCertificate.coefficientControlled
    (c : CoefficientEnvelopeRefinementCertificate) : Prop :=
  c.coefficientWindow ≤ c.envelopeWindow + c.errorSlackWindow + c.slack

def CoefficientEnvelopeRefinementCertificate.envelopeBudgetControlled
    (c : CoefficientEnvelopeRefinementCertificate) : Prop :=
  c.envelopeBudgetWindow ≤
    c.envelopeWindow + c.coefficientWindow + c.errorSlackWindow + c.slack

def coefficientEnvelopeRefinementReady
    (c : CoefficientEnvelopeRefinementCertificate) : Prop :=
  0 < c.envelopeWindow ∧
    c.coefficientControlled ∧
    c.envelopeBudgetControlled

def CoefficientEnvelopeRefinementCertificate.size
    (c : CoefficientEnvelopeRefinementCertificate) : ℕ :=
  c.envelopeWindow + c.coefficientWindow + c.errorSlackWindow + c.slack

theorem coefficientEnvelope_envelopeBudgetWindow_le_size
    {c : CoefficientEnvelopeRefinementCertificate}
    (h : coefficientEnvelopeRefinementReady c) :
    c.envelopeBudgetWindow ≤ c.size := by
  rcases h with ⟨_, _, hbudget⟩
  exact hbudget

def sampleCoefficientEnvelopeRefinementCertificate :
    CoefficientEnvelopeRefinementCertificate :=
  { envelopeWindow := 6, coefficientWindow := 7, errorSlackWindow := 2,
    envelopeBudgetWindow := 16, slack := 1 }

example : coefficientEnvelopeRefinementReady
    sampleCoefficientEnvelopeRefinementCertificate := by
  norm_num [coefficientEnvelopeRefinementReady,
    CoefficientEnvelopeRefinementCertificate.coefficientControlled,
    CoefficientEnvelopeRefinementCertificate.envelopeBudgetControlled,
    sampleCoefficientEnvelopeRefinementCertificate]

example :
    sampleCoefficientEnvelopeRefinementCertificate.envelopeBudgetWindow ≤
      sampleCoefficientEnvelopeRefinementCertificate.size := by
  norm_num [CoefficientEnvelopeRefinementCertificate.size,
    sampleCoefficientEnvelopeRefinementCertificate]

/-- A second-stage coefficient envelope certificate with an external budget. -/
structure CoefficientEnvelopeBudgetCertificate where
  envelopeWindow : ℕ
  coefficientWindow : ℕ
  errorSlackWindow : ℕ
  envelopeBudgetWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def CoefficientEnvelopeBudgetCertificate.envelopeControlled
    (cert : CoefficientEnvelopeBudgetCertificate) : Prop :=
  0 < cert.envelopeWindow ∧
    cert.coefficientWindow ≤ cert.envelopeWindow + cert.errorSlackWindow + cert.slack ∧
      cert.envelopeBudgetWindow ≤
        cert.envelopeWindow + cert.coefficientWindow + cert.errorSlackWindow + cert.slack

def CoefficientEnvelopeBudgetCertificate.budgetControlled
    (cert : CoefficientEnvelopeBudgetCertificate) : Prop :=
  cert.certificateBudgetWindow ≤
    cert.envelopeWindow + cert.coefficientWindow + cert.errorSlackWindow +
      cert.envelopeBudgetWindow + cert.slack

def coefficientEnvelopeBudgetReady
    (cert : CoefficientEnvelopeBudgetCertificate) : Prop :=
  cert.envelopeControlled ∧ cert.budgetControlled

def CoefficientEnvelopeBudgetCertificate.size
    (cert : CoefficientEnvelopeBudgetCertificate) : ℕ :=
  cert.envelopeWindow + cert.coefficientWindow + cert.errorSlackWindow +
    cert.envelopeBudgetWindow + cert.slack

theorem coefficientEnvelope_certificateBudgetWindow_le_size
    (cert : CoefficientEnvelopeBudgetCertificate)
    (h : coefficientEnvelopeBudgetReady cert) :
    cert.certificateBudgetWindow ≤ cert.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleCoefficientEnvelopeBudgetCertificate :
    CoefficientEnvelopeBudgetCertificate :=
  { envelopeWindow := 6, coefficientWindow := 7, errorSlackWindow := 2,
    envelopeBudgetWindow := 16, certificateBudgetWindow := 32, slack := 1 }

example :
    coefficientEnvelopeBudgetReady sampleCoefficientEnvelopeBudgetCertificate := by
  norm_num [coefficientEnvelopeBudgetReady,
    CoefficientEnvelopeBudgetCertificate.envelopeControlled,
    CoefficientEnvelopeBudgetCertificate.budgetControlled,
    sampleCoefficientEnvelopeBudgetCertificate]

example :
    sampleCoefficientEnvelopeBudgetCertificate.certificateBudgetWindow ≤
      sampleCoefficientEnvelopeBudgetCertificate.size := by
  apply coefficientEnvelope_certificateBudgetWindow_le_size
  norm_num [coefficientEnvelopeBudgetReady,
    CoefficientEnvelopeBudgetCertificate.envelopeControlled,
    CoefficientEnvelopeBudgetCertificate.budgetControlled,
    sampleCoefficientEnvelopeBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    coefficientEnvelopeBudgetReady sampleCoefficientEnvelopeBudgetCertificate := by
  constructor
  · norm_num [CoefficientEnvelopeBudgetCertificate.envelopeControlled,
      sampleCoefficientEnvelopeBudgetCertificate]
  · norm_num [CoefficientEnvelopeBudgetCertificate.budgetControlled,
      sampleCoefficientEnvelopeBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleCoefficientEnvelopeBudgetCertificate.certificateBudgetWindow ≤
      sampleCoefficientEnvelopeBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady
    (data : List CoefficientEnvelopeBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleCoefficientEnvelopeBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleCoefficientEnvelopeBudgetCertificate
  native_decide
end AnalyticCombinatorics.Asymptotics.CoefficientEnvelopeSchemas
