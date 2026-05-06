import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Uniform moment envelopes.

The finite record stores moment order, envelope height, and error slack.
-/

namespace AnalyticCombinatorics.Asymptotics.UniformMomentEnvelopes

structure UniformMomentEnvelopeData where
  momentOrder : ℕ
  envelopeHeight : ℕ
  errorSlack : ℕ
deriving DecidableEq, Repr

def momentOrderPositive (d : UniformMomentEnvelopeData) : Prop :=
  0 < d.momentOrder

def envelopeControlled (d : UniformMomentEnvelopeData) : Prop :=
  d.envelopeHeight ≤ d.momentOrder + d.errorSlack

def uniformMomentEnvelopeReady (d : UniformMomentEnvelopeData) : Prop :=
  momentOrderPositive d ∧ envelopeControlled d

def uniformMomentEnvelopeBudget (d : UniformMomentEnvelopeData) : ℕ :=
  d.momentOrder + d.envelopeHeight + d.errorSlack

theorem uniformMomentEnvelopeReady.order
    {d : UniformMomentEnvelopeData}
    (h : uniformMomentEnvelopeReady d) :
    momentOrderPositive d ∧ envelopeControlled d ∧
      d.envelopeHeight ≤ uniformMomentEnvelopeBudget d := by
  refine ⟨h.1, h.2, ?_⟩
  unfold uniformMomentEnvelopeBudget
  omega

theorem envelopeHeight_le_momentEnvelopeBudget
    (d : UniformMomentEnvelopeData) :
    d.envelopeHeight ≤ uniformMomentEnvelopeBudget d := by
  unfold uniformMomentEnvelopeBudget
  omega

def sampleUniformMomentEnvelopeData : UniformMomentEnvelopeData :=
  { momentOrder := 5, envelopeHeight := 7, errorSlack := 3 }

example : uniformMomentEnvelopeReady sampleUniformMomentEnvelopeData := by
  norm_num [uniformMomentEnvelopeReady, momentOrderPositive]
  norm_num [envelopeControlled, sampleUniformMomentEnvelopeData]

example : uniformMomentEnvelopeBudget sampleUniformMomentEnvelopeData = 15 := by
  native_decide

/-- Finite executable readiness audit for uniform moment envelopes. -/
def uniformMomentEnvelopeDataListReady
    (data : List UniformMomentEnvelopeData) : Bool :=
  data.all fun d =>
    0 < d.momentOrder && d.envelopeHeight ≤ d.momentOrder + d.errorSlack

theorem uniformMomentEnvelopeDataList_readyWindow :
    uniformMomentEnvelopeDataListReady
      [{ momentOrder := 4, envelopeHeight := 5, errorSlack := 1 },
       { momentOrder := 5, envelopeHeight := 7, errorSlack := 3 }] = true := by
  unfold uniformMomentEnvelopeDataListReady
  native_decide

/-- A certificate window for uniform moment envelopes. -/
structure UniformMomentEnvelopeCertificateWindow where
  momentWindow : ℕ
  envelopeWindow : ℕ
  errorSlack : ℕ
  certificateBudget : ℕ
  slack : ℕ

/-- The envelope window is controlled by moment order and slack. -/
def uniformMomentEnvelopeCertificateControlled
    (w : UniformMomentEnvelopeCertificateWindow) : Prop :=
  w.envelopeWindow ≤ w.momentWindow + w.errorSlack + w.slack

/-- Readiness for a moment envelope certificate. -/
def uniformMomentEnvelopeCertificateReady
    (w : UniformMomentEnvelopeCertificateWindow) : Prop :=
  0 < w.momentWindow ∧
    uniformMomentEnvelopeCertificateControlled w ∧
      w.certificateBudget ≤ w.momentWindow + w.envelopeWindow + w.slack

/-- Total size of a moment envelope certificate. -/
def uniformMomentEnvelopeCertificate
    (w : UniformMomentEnvelopeCertificateWindow) : ℕ :=
  w.momentWindow + w.envelopeWindow + w.errorSlack + w.certificateBudget + w.slack

theorem uniformMomentEnvelopeCertificate_budget_le_certificate
    (w : UniformMomentEnvelopeCertificateWindow)
    (h : uniformMomentEnvelopeCertificateReady w) :
    w.certificateBudget ≤ uniformMomentEnvelopeCertificate w := by
  rcases h with ⟨_, _, hbudget⟩
  unfold uniformMomentEnvelopeCertificate
  omega

def sampleUniformMomentEnvelopeCertificateWindow :
    UniformMomentEnvelopeCertificateWindow where
  momentWindow := 5
  envelopeWindow := 6
  errorSlack := 2
  certificateBudget := 10
  slack := 1

example :
    uniformMomentEnvelopeCertificateReady
      sampleUniformMomentEnvelopeCertificateWindow := by
  norm_num [uniformMomentEnvelopeCertificateReady,
    uniformMomentEnvelopeCertificateControlled,
    sampleUniformMomentEnvelopeCertificateWindow]

example :
    sampleUniformMomentEnvelopeCertificateWindow.certificateBudget ≤
      uniformMomentEnvelopeCertificate
        sampleUniformMomentEnvelopeCertificateWindow := by
  apply uniformMomentEnvelopeCertificate_budget_le_certificate
  norm_num [uniformMomentEnvelopeCertificateReady,
    uniformMomentEnvelopeCertificateControlled,
    sampleUniformMomentEnvelopeCertificateWindow]

structure UniformMomentEnvelopeRefinementCertificate where
  momentWindow : ℕ
  envelopeWindow : ℕ
  errorSlackWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def UniformMomentEnvelopeRefinementCertificate.envelopeControlled
    (c : UniformMomentEnvelopeRefinementCertificate) : Prop :=
  c.envelopeWindow ≤ c.momentWindow + c.errorSlackWindow + c.slack

def UniformMomentEnvelopeRefinementCertificate.certificateBudgetControlled
    (c : UniformMomentEnvelopeRefinementCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.momentWindow + c.envelopeWindow + c.errorSlackWindow + c.slack

def uniformMomentEnvelopeRefinementReady
    (c : UniformMomentEnvelopeRefinementCertificate) : Prop :=
  0 < c.momentWindow ∧ c.envelopeControlled ∧ c.certificateBudgetControlled

def UniformMomentEnvelopeRefinementCertificate.size
    (c : UniformMomentEnvelopeRefinementCertificate) : ℕ :=
  c.momentWindow + c.envelopeWindow + c.errorSlackWindow + c.slack

theorem uniformMomentEnvelope_certificateBudgetWindow_le_size
    {c : UniformMomentEnvelopeRefinementCertificate}
    (h : uniformMomentEnvelopeRefinementReady c) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, _, hbudget⟩
  exact hbudget

def sampleUniformMomentEnvelopeRefinementCertificate :
    UniformMomentEnvelopeRefinementCertificate :=
  { momentWindow := 5, envelopeWindow := 6, errorSlackWindow := 2,
    certificateBudgetWindow := 14, slack := 1 }

example : uniformMomentEnvelopeRefinementReady
    sampleUniformMomentEnvelopeRefinementCertificate := by
  norm_num [uniformMomentEnvelopeRefinementReady,
    UniformMomentEnvelopeRefinementCertificate.envelopeControlled,
    UniformMomentEnvelopeRefinementCertificate.certificateBudgetControlled,
    sampleUniformMomentEnvelopeRefinementCertificate]

example :
    sampleUniformMomentEnvelopeRefinementCertificate.certificateBudgetWindow ≤
      sampleUniformMomentEnvelopeRefinementCertificate.size := by
  norm_num [UniformMomentEnvelopeRefinementCertificate.size,
    sampleUniformMomentEnvelopeRefinementCertificate]

structure UniformMomentEnvelopeBudgetCertificate where
  momentWindow : ℕ
  envelopeWindow : ℕ
  errorSlackWindow : ℕ
  envelopeBudgetWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def UniformMomentEnvelopeBudgetCertificate.controlled
    (c : UniformMomentEnvelopeBudgetCertificate) : Prop :=
  0 < c.momentWindow ∧
    c.envelopeWindow ≤ c.momentWindow + c.errorSlackWindow + c.slack ∧
      c.envelopeBudgetWindow ≤
        c.momentWindow + c.envelopeWindow + c.errorSlackWindow + c.slack

def UniformMomentEnvelopeBudgetCertificate.budgetControlled
    (c : UniformMomentEnvelopeBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.momentWindow + c.envelopeWindow + c.errorSlackWindow +
      c.envelopeBudgetWindow + c.slack

def UniformMomentEnvelopeBudgetCertificate.Ready
    (c : UniformMomentEnvelopeBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def UniformMomentEnvelopeBudgetCertificate.size
    (c : UniformMomentEnvelopeBudgetCertificate) : ℕ :=
  c.momentWindow + c.envelopeWindow + c.errorSlackWindow +
    c.envelopeBudgetWindow + c.slack

theorem uniformMomentEnvelope_budgetCertificate_le_size
    (c : UniformMomentEnvelopeBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleUniformMomentEnvelopeBudgetCertificate :
    UniformMomentEnvelopeBudgetCertificate :=
  { momentWindow := 5
    envelopeWindow := 6
    errorSlackWindow := 2
    envelopeBudgetWindow := 14
    certificateBudgetWindow := 28
    slack := 1 }

example : sampleUniformMomentEnvelopeBudgetCertificate.Ready := by
  constructor
  · norm_num [UniformMomentEnvelopeBudgetCertificate.controlled,
      sampleUniformMomentEnvelopeBudgetCertificate]
  · norm_num [UniformMomentEnvelopeBudgetCertificate.budgetControlled,
      sampleUniformMomentEnvelopeBudgetCertificate]

example :
    sampleUniformMomentEnvelopeBudgetCertificate.certificateBudgetWindow ≤
      sampleUniformMomentEnvelopeBudgetCertificate.size := by
  apply uniformMomentEnvelope_budgetCertificate_le_size
  constructor
  · norm_num [UniformMomentEnvelopeBudgetCertificate.controlled,
      sampleUniformMomentEnvelopeBudgetCertificate]
  · norm_num [UniformMomentEnvelopeBudgetCertificate.budgetControlled,
      sampleUniformMomentEnvelopeBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleUniformMomentEnvelopeBudgetCertificate.Ready := by
  constructor
  · norm_num [UniformMomentEnvelopeBudgetCertificate.controlled,
      sampleUniformMomentEnvelopeBudgetCertificate]
  · norm_num [UniformMomentEnvelopeBudgetCertificate.budgetControlled,
      sampleUniformMomentEnvelopeBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleUniformMomentEnvelopeBudgetCertificate.certificateBudgetWindow ≤
      sampleUniformMomentEnvelopeBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady
    (data : List UniformMomentEnvelopeBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleUniformMomentEnvelopeBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleUniformMomentEnvelopeBudgetCertificate
  native_decide
end AnalyticCombinatorics.Asymptotics.UniformMomentEnvelopes
