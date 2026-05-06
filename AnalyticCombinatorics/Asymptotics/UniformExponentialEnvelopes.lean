import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Uniform exponential envelopes.

The finite schema records exponential scale, envelope budget, and error
slack.
-/

namespace AnalyticCombinatorics.Asymptotics.UniformExponentialEnvelopes

structure UniformExponentialEnvelopeData where
  exponentialScale : ℕ
  envelopeBudget : ℕ
  errorSlack : ℕ
deriving DecidableEq, Repr

def exponentialScalePositive (d : UniformExponentialEnvelopeData) : Prop :=
  0 < d.exponentialScale

def envelopeControlled (d : UniformExponentialEnvelopeData) : Prop :=
  d.envelopeBudget ≤ d.exponentialScale + d.errorSlack

def uniformExponentialEnvelopeReady
    (d : UniformExponentialEnvelopeData) : Prop :=
  exponentialScalePositive d ∧ envelopeControlled d

def uniformExponentialEnvelopeBudget
    (d : UniformExponentialEnvelopeData) : ℕ :=
  d.exponentialScale + d.envelopeBudget + d.errorSlack

theorem uniformExponentialEnvelopeReady.scale
    {d : UniformExponentialEnvelopeData}
    (h : uniformExponentialEnvelopeReady d) :
    exponentialScalePositive d ∧ envelopeControlled d ∧
      d.envelopeBudget ≤ uniformExponentialEnvelopeBudget d := by
  refine ⟨h.1, h.2, ?_⟩
  unfold uniformExponentialEnvelopeBudget
  omega

theorem envelopeBudget_le_exponentialEnvelopeBudget
    (d : UniformExponentialEnvelopeData) :
    d.envelopeBudget ≤ uniformExponentialEnvelopeBudget d := by
  unfold uniformExponentialEnvelopeBudget
  omega

def sampleUniformExponentialEnvelopeData :
    UniformExponentialEnvelopeData :=
  { exponentialScale := 6, envelopeBudget := 8, errorSlack := 3 }

example :
    uniformExponentialEnvelopeReady sampleUniformExponentialEnvelopeData := by
  norm_num [uniformExponentialEnvelopeReady, exponentialScalePositive]
  norm_num [envelopeControlled, sampleUniformExponentialEnvelopeData]

example :
    uniformExponentialEnvelopeBudget
      sampleUniformExponentialEnvelopeData = 17 := by
  native_decide

/-- Finite executable readiness audit for uniform exponential envelopes. -/
def uniformExponentialEnvelopeDataListReady
    (data : List UniformExponentialEnvelopeData) : Bool :=
  data.all fun d =>
    0 < d.exponentialScale && d.envelopeBudget ≤ d.exponentialScale + d.errorSlack

theorem uniformExponentialEnvelopeDataList_readyWindow :
    uniformExponentialEnvelopeDataListReady
      [{ exponentialScale := 4, envelopeBudget := 5, errorSlack := 1 },
       { exponentialScale := 6, envelopeBudget := 8, errorSlack := 3 }] = true := by
  unfold uniformExponentialEnvelopeDataListReady
  native_decide

/-- A certificate window for uniform exponential envelopes. -/
structure UniformExponentialEnvelopeCertificateWindow where
  exponentialWindow : ℕ
  envelopeWindow : ℕ
  errorSlack : ℕ
  certificateBudget : ℕ
  slack : ℕ

/-- The envelope window is controlled by exponential scale and slack. -/
def uniformExponentialEnvelopeCertificateControlled
    (w : UniformExponentialEnvelopeCertificateWindow) : Prop :=
  w.envelopeWindow ≤ w.exponentialWindow + w.errorSlack + w.slack

/-- Readiness for an exponential envelope certificate. -/
def uniformExponentialEnvelopeCertificateReady
    (w : UniformExponentialEnvelopeCertificateWindow) : Prop :=
  0 < w.exponentialWindow ∧
    uniformExponentialEnvelopeCertificateControlled w ∧
      w.certificateBudget ≤ w.exponentialWindow + w.envelopeWindow + w.slack

/-- Total size of an exponential envelope certificate. -/
def uniformExponentialEnvelopeCertificate
    (w : UniformExponentialEnvelopeCertificateWindow) : ℕ :=
  w.exponentialWindow + w.envelopeWindow + w.errorSlack +
    w.certificateBudget + w.slack

theorem uniformExponentialEnvelopeCertificate_budget_le_certificate
    (w : UniformExponentialEnvelopeCertificateWindow)
    (h : uniformExponentialEnvelopeCertificateReady w) :
    w.certificateBudget ≤ uniformExponentialEnvelopeCertificate w := by
  rcases h with ⟨_, _, hbudget⟩
  unfold uniformExponentialEnvelopeCertificate
  omega

def sampleUniformExponentialEnvelopeCertificateWindow :
    UniformExponentialEnvelopeCertificateWindow where
  exponentialWindow := 6
  envelopeWindow := 7
  errorSlack := 2
  certificateBudget := 12
  slack := 1

example :
    uniformExponentialEnvelopeCertificateReady
      sampleUniformExponentialEnvelopeCertificateWindow := by
  norm_num [uniformExponentialEnvelopeCertificateReady,
    uniformExponentialEnvelopeCertificateControlled,
    sampleUniformExponentialEnvelopeCertificateWindow]

example :
    sampleUniformExponentialEnvelopeCertificateWindow.certificateBudget ≤
      uniformExponentialEnvelopeCertificate
        sampleUniformExponentialEnvelopeCertificateWindow := by
  apply uniformExponentialEnvelopeCertificate_budget_le_certificate
  norm_num [uniformExponentialEnvelopeCertificateReady,
    uniformExponentialEnvelopeCertificateControlled,
    sampleUniformExponentialEnvelopeCertificateWindow]

structure UniformExponentialEnvelopeRefinementCertificate where
  exponentialWindow : ℕ
  envelopeWindow : ℕ
  errorSlackWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def UniformExponentialEnvelopeRefinementCertificate.envelopeControlled
    (c : UniformExponentialEnvelopeRefinementCertificate) : Prop :=
  c.envelopeWindow ≤ c.exponentialWindow + c.errorSlackWindow + c.slack

def UniformExponentialEnvelopeRefinementCertificate.certificateBudgetControlled
    (c : UniformExponentialEnvelopeRefinementCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.exponentialWindow + c.envelopeWindow + c.errorSlackWindow + c.slack

def uniformExponentialEnvelopeRefinementReady
    (c : UniformExponentialEnvelopeRefinementCertificate) : Prop :=
  0 < c.exponentialWindow ∧ c.envelopeControlled ∧ c.certificateBudgetControlled

def UniformExponentialEnvelopeRefinementCertificate.size
    (c : UniformExponentialEnvelopeRefinementCertificate) : ℕ :=
  c.exponentialWindow + c.envelopeWindow + c.errorSlackWindow + c.slack

theorem uniformExponentialEnvelope_certificateBudgetWindow_le_size
    {c : UniformExponentialEnvelopeRefinementCertificate}
    (h : uniformExponentialEnvelopeRefinementReady c) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, _, hbudget⟩
  exact hbudget

def sampleUniformExponentialEnvelopeRefinementCertificate :
    UniformExponentialEnvelopeRefinementCertificate :=
  { exponentialWindow := 6, envelopeWindow := 7, errorSlackWindow := 2,
    certificateBudgetWindow := 16, slack := 1 }

example : uniformExponentialEnvelopeRefinementReady
    sampleUniformExponentialEnvelopeRefinementCertificate := by
  norm_num [uniformExponentialEnvelopeRefinementReady,
    UniformExponentialEnvelopeRefinementCertificate.envelopeControlled,
    UniformExponentialEnvelopeRefinementCertificate.certificateBudgetControlled,
    sampleUniformExponentialEnvelopeRefinementCertificate]

example :
    sampleUniformExponentialEnvelopeRefinementCertificate.certificateBudgetWindow ≤
      sampleUniformExponentialEnvelopeRefinementCertificate.size := by
  norm_num [UniformExponentialEnvelopeRefinementCertificate.size,
    sampleUniformExponentialEnvelopeRefinementCertificate]

structure UniformExponentialEnvelopeBudgetCertificate where
  exponentialWindow : ℕ
  envelopeWindow : ℕ
  errorSlackWindow : ℕ
  envelopeBudgetWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def UniformExponentialEnvelopeBudgetCertificate.controlled
    (c : UniformExponentialEnvelopeBudgetCertificate) : Prop :=
  0 < c.exponentialWindow ∧
    c.envelopeWindow ≤ c.exponentialWindow + c.errorSlackWindow + c.slack ∧
      c.envelopeBudgetWindow ≤
        c.exponentialWindow + c.envelopeWindow + c.errorSlackWindow + c.slack

def UniformExponentialEnvelopeBudgetCertificate.budgetControlled
    (c : UniformExponentialEnvelopeBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.exponentialWindow + c.envelopeWindow + c.errorSlackWindow +
      c.envelopeBudgetWindow + c.slack

def UniformExponentialEnvelopeBudgetCertificate.Ready
    (c : UniformExponentialEnvelopeBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def UniformExponentialEnvelopeBudgetCertificate.size
    (c : UniformExponentialEnvelopeBudgetCertificate) : ℕ :=
  c.exponentialWindow + c.envelopeWindow + c.errorSlackWindow +
    c.envelopeBudgetWindow + c.slack

theorem uniformExponentialEnvelope_budgetCertificate_le_size
    (c : UniformExponentialEnvelopeBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleUniformExponentialEnvelopeBudgetCertificate :
    UniformExponentialEnvelopeBudgetCertificate :=
  { exponentialWindow := 6
    envelopeWindow := 7
    errorSlackWindow := 2
    envelopeBudgetWindow := 16
    certificateBudgetWindow := 32
    slack := 1 }

example : sampleUniformExponentialEnvelopeBudgetCertificate.Ready := by
  constructor
  · norm_num [UniformExponentialEnvelopeBudgetCertificate.controlled,
      sampleUniformExponentialEnvelopeBudgetCertificate]
  · norm_num [UniformExponentialEnvelopeBudgetCertificate.budgetControlled,
      sampleUniformExponentialEnvelopeBudgetCertificate]

example :
    sampleUniformExponentialEnvelopeBudgetCertificate.certificateBudgetWindow ≤
      sampleUniformExponentialEnvelopeBudgetCertificate.size := by
  apply uniformExponentialEnvelope_budgetCertificate_le_size
  constructor
  · norm_num [UniformExponentialEnvelopeBudgetCertificate.controlled,
      sampleUniformExponentialEnvelopeBudgetCertificate]
  · norm_num [UniformExponentialEnvelopeBudgetCertificate.budgetControlled,
      sampleUniformExponentialEnvelopeBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleUniformExponentialEnvelopeBudgetCertificate.Ready := by
  constructor
  · norm_num [UniformExponentialEnvelopeBudgetCertificate.controlled,
      sampleUniformExponentialEnvelopeBudgetCertificate]
  · norm_num [UniformExponentialEnvelopeBudgetCertificate.budgetControlled,
      sampleUniformExponentialEnvelopeBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleUniformExponentialEnvelopeBudgetCertificate.certificateBudgetWindow ≤
      sampleUniformExponentialEnvelopeBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady
    (data : List UniformExponentialEnvelopeBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleUniformExponentialEnvelopeBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleUniformExponentialEnvelopeBudgetCertificate
  native_decide
end AnalyticCombinatorics.Asymptotics.UniformExponentialEnvelopes
