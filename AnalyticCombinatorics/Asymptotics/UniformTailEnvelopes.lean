import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Uniform tail envelopes.

The finite schema records tail cutoff, envelope scale, and error slack.
-/

namespace AnalyticCombinatorics.Asymptotics.UniformTailEnvelopes

structure UniformTailEnvelopeData where
  tailCutoff : ℕ
  envelopeScale : ℕ
  errorSlack : ℕ
deriving DecidableEq, Repr

def envelopeScalePositive (d : UniformTailEnvelopeData) : Prop :=
  0 < d.envelopeScale

def tailCutoffControlled (d : UniformTailEnvelopeData) : Prop :=
  d.tailCutoff ≤ d.envelopeScale + d.errorSlack

def uniformTailEnvelopeReady (d : UniformTailEnvelopeData) : Prop :=
  envelopeScalePositive d ∧ tailCutoffControlled d

def uniformTailEnvelopeBudget (d : UniformTailEnvelopeData) : ℕ :=
  d.tailCutoff + d.envelopeScale + d.errorSlack

theorem uniformTailEnvelopeReady.scale {d : UniformTailEnvelopeData}
    (h : uniformTailEnvelopeReady d) :
    envelopeScalePositive d ∧ tailCutoffControlled d ∧
      d.tailCutoff ≤ uniformTailEnvelopeBudget d := by
  refine ⟨h.1, h.2, ?_⟩
  unfold uniformTailEnvelopeBudget
  omega

theorem tailCutoff_le_tailEnvelopeBudget (d : UniformTailEnvelopeData) :
    d.tailCutoff ≤ uniformTailEnvelopeBudget d := by
  unfold uniformTailEnvelopeBudget
  omega

def sampleUniformTailEnvelopeData : UniformTailEnvelopeData :=
  { tailCutoff := 7, envelopeScale := 5, errorSlack := 3 }

example : uniformTailEnvelopeReady sampleUniformTailEnvelopeData := by
  norm_num [uniformTailEnvelopeReady, envelopeScalePositive]
  norm_num [tailCutoffControlled, sampleUniformTailEnvelopeData]

example : uniformTailEnvelopeBudget sampleUniformTailEnvelopeData = 15 := by
  native_decide

/-- Finite executable readiness audit for uniform tail envelopes. -/
def uniformTailEnvelopeDataListReady
    (data : List UniformTailEnvelopeData) : Bool :=
  data.all fun d =>
    0 < d.envelopeScale && d.tailCutoff ≤ d.envelopeScale + d.errorSlack

theorem uniformTailEnvelopeDataList_readyWindow :
    uniformTailEnvelopeDataListReady
      [{ tailCutoff := 4, envelopeScale := 5, errorSlack := 1 },
       { tailCutoff := 7, envelopeScale := 5, errorSlack := 3 }] = true := by
  unfold uniformTailEnvelopeDataListReady
  native_decide

structure UniformTailEnvelopeWindow where
  cutoffWindow : ℕ
  envelopeWindow : ℕ
  errorSlack : ℕ
  tailBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def UniformTailEnvelopeWindow.cutoffControlled
    (w : UniformTailEnvelopeWindow) : Prop :=
  w.cutoffWindow ≤ w.envelopeWindow + w.errorSlack + w.slack

def uniformTailEnvelopeWindowReady (w : UniformTailEnvelopeWindow) : Prop :=
  0 < w.envelopeWindow ∧ w.cutoffControlled ∧
    w.tailBudget ≤ w.cutoffWindow + w.envelopeWindow + w.slack

def UniformTailEnvelopeWindow.certificate
    (w : UniformTailEnvelopeWindow) : ℕ :=
  w.cutoffWindow + w.envelopeWindow + w.errorSlack + w.tailBudget + w.slack

theorem uniformTailEnvelope_budget_le_certificate
    (w : UniformTailEnvelopeWindow) :
    w.tailBudget ≤ w.certificate := by
  unfold UniformTailEnvelopeWindow.certificate
  omega

def sampleUniformTailEnvelopeWindow : UniformTailEnvelopeWindow :=
  { cutoffWindow := 6, envelopeWindow := 5, errorSlack := 2,
    tailBudget := 12, slack := 1 }

example : uniformTailEnvelopeWindowReady sampleUniformTailEnvelopeWindow := by
  norm_num [uniformTailEnvelopeWindowReady,
    UniformTailEnvelopeWindow.cutoffControlled, sampleUniformTailEnvelopeWindow]

/-- A refinement certificate for uniform tail envelopes. -/
structure UniformTailEnvelopeCertificate where
  cutoffWindow : ℕ
  envelopeWindow : ℕ
  errorSlackWindow : ℕ
  tailBudgetWindow : ℕ
  slack : ℕ

/-- Cutoff and tail budgets are controlled by a uniform envelope. -/
def uniformTailEnvelopeCertificateControlled
    (w : UniformTailEnvelopeCertificate) : Prop :=
  0 < w.envelopeWindow ∧
    w.cutoffWindow ≤ w.envelopeWindow + w.errorSlackWindow + w.slack ∧
      w.tailBudgetWindow ≤ w.cutoffWindow + w.envelopeWindow + w.slack

/-- Readiness for a uniform tail envelope certificate. -/
def uniformTailEnvelopeCertificateReady
    (w : UniformTailEnvelopeCertificate) : Prop :=
  uniformTailEnvelopeCertificateControlled w ∧
    w.tailBudgetWindow ≤
      w.cutoffWindow + w.envelopeWindow + w.errorSlackWindow +
        w.tailBudgetWindow + w.slack

/-- Total size of a uniform tail envelope certificate. -/
def uniformTailEnvelopeCertificateSize
    (w : UniformTailEnvelopeCertificate) : ℕ :=
  w.cutoffWindow + w.envelopeWindow + w.errorSlackWindow + w.tailBudgetWindow + w.slack

theorem uniformTailEnvelopeCertificate_budget_le_size
    (w : UniformTailEnvelopeCertificate)
    (h : uniformTailEnvelopeCertificateReady w) :
    w.tailBudgetWindow ≤ uniformTailEnvelopeCertificateSize w := by
  rcases h with ⟨_, hbudget⟩
  unfold uniformTailEnvelopeCertificateSize
  omega

def sampleUniformTailEnvelopeCertificate :
    UniformTailEnvelopeCertificate where
  cutoffWindow := 6
  envelopeWindow := 5
  errorSlackWindow := 2
  tailBudgetWindow := 12
  slack := 1

example :
    uniformTailEnvelopeCertificateReady
      sampleUniformTailEnvelopeCertificate := by
  norm_num [uniformTailEnvelopeCertificateReady,
    uniformTailEnvelopeCertificateControlled, sampleUniformTailEnvelopeCertificate]

example :
    sampleUniformTailEnvelopeCertificate.tailBudgetWindow ≤
      uniformTailEnvelopeCertificateSize sampleUniformTailEnvelopeCertificate := by
  apply uniformTailEnvelopeCertificate_budget_le_size
  norm_num [uniformTailEnvelopeCertificateReady,
    uniformTailEnvelopeCertificateControlled, sampleUniformTailEnvelopeCertificate]

/-- A refinement certificate with the uniform-tail budget separated from size. -/
structure UniformTailEnvelopeRefinementCertificate where
  cutoffWindow : ℕ
  envelopeWindow : ℕ
  errorSlackWindow : ℕ
  tailBudgetWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def UniformTailEnvelopeRefinementCertificate.tailControlled
    (cert : UniformTailEnvelopeRefinementCertificate) : Prop :=
  0 < cert.envelopeWindow ∧
    cert.cutoffWindow ≤ cert.envelopeWindow + cert.errorSlackWindow + cert.slack ∧
      cert.tailBudgetWindow ≤ cert.cutoffWindow + cert.envelopeWindow + cert.slack

def UniformTailEnvelopeRefinementCertificate.budgetControlled
    (cert : UniformTailEnvelopeRefinementCertificate) : Prop :=
  cert.certificateBudgetWindow ≤
    cert.cutoffWindow + cert.envelopeWindow + cert.errorSlackWindow +
      cert.tailBudgetWindow + cert.slack

def uniformTailEnvelopeRefinementReady
    (cert : UniformTailEnvelopeRefinementCertificate) : Prop :=
  cert.tailControlled ∧ cert.budgetControlled

def UniformTailEnvelopeRefinementCertificate.size
    (cert : UniformTailEnvelopeRefinementCertificate) : ℕ :=
  cert.cutoffWindow + cert.envelopeWindow + cert.errorSlackWindow +
    cert.tailBudgetWindow + cert.slack

theorem uniformTailEnvelope_certificateBudgetWindow_le_size
    (cert : UniformTailEnvelopeRefinementCertificate)
    (h : uniformTailEnvelopeRefinementReady cert) :
    cert.certificateBudgetWindow ≤ cert.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleUniformTailEnvelopeRefinementCertificate :
    UniformTailEnvelopeRefinementCertificate :=
  { cutoffWindow := 6, envelopeWindow := 5, errorSlackWindow := 2,
    tailBudgetWindow := 12, certificateBudgetWindow := 26, slack := 1 }

example :
    uniformTailEnvelopeRefinementReady
      sampleUniformTailEnvelopeRefinementCertificate := by
  norm_num [uniformTailEnvelopeRefinementReady,
    UniformTailEnvelopeRefinementCertificate.tailControlled,
    UniformTailEnvelopeRefinementCertificate.budgetControlled,
    sampleUniformTailEnvelopeRefinementCertificate]

example :
    sampleUniformTailEnvelopeRefinementCertificate.certificateBudgetWindow ≤
      sampleUniformTailEnvelopeRefinementCertificate.size := by
  apply uniformTailEnvelope_certificateBudgetWindow_le_size
  norm_num [uniformTailEnvelopeRefinementReady,
    UniformTailEnvelopeRefinementCertificate.tailControlled,
    UniformTailEnvelopeRefinementCertificate.budgetControlled,
    sampleUniformTailEnvelopeRefinementCertificate]


structure UniformTailEnvelopesBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def UniformTailEnvelopesBudgetCertificate.controlled
    (c : UniformTailEnvelopesBudgetCertificate) : Prop :=
  0 < c.primaryWindow ∧ c.secondaryWindow ≤ c.primaryWindow + c.slack

def UniformTailEnvelopesBudgetCertificate.budgetControlled
    (c : UniformTailEnvelopesBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def UniformTailEnvelopesBudgetCertificate.Ready
    (c : UniformTailEnvelopesBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def UniformTailEnvelopesBudgetCertificate.size
    (c : UniformTailEnvelopesBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem uniformTailEnvelopes_budgetCertificate_le_size
    (c : UniformTailEnvelopesBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleUniformTailEnvelopesBudgetCertificate :
    UniformTailEnvelopesBudgetCertificate :=
  { primaryWindow := 5
    secondaryWindow := 6
    certificateBudgetWindow := 12
    slack := 1 }

example : sampleUniformTailEnvelopesBudgetCertificate.Ready := by
  constructor
  · norm_num [UniformTailEnvelopesBudgetCertificate.controlled,
      sampleUniformTailEnvelopesBudgetCertificate]
  · norm_num [UniformTailEnvelopesBudgetCertificate.budgetControlled,
      sampleUniformTailEnvelopesBudgetCertificate]

example :
    sampleUniformTailEnvelopesBudgetCertificate.certificateBudgetWindow ≤
      sampleUniformTailEnvelopesBudgetCertificate.size := by
  apply uniformTailEnvelopes_budgetCertificate_le_size
  constructor
  · norm_num [UniformTailEnvelopesBudgetCertificate.controlled,
      sampleUniformTailEnvelopesBudgetCertificate]
  · norm_num [UniformTailEnvelopesBudgetCertificate.budgetControlled,
      sampleUniformTailEnvelopesBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleUniformTailEnvelopesBudgetCertificate.Ready := by
  constructor
  · norm_num [UniformTailEnvelopesBudgetCertificate.controlled,
      sampleUniformTailEnvelopesBudgetCertificate]
  · norm_num [UniformTailEnvelopesBudgetCertificate.budgetControlled,
      sampleUniformTailEnvelopesBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleUniformTailEnvelopesBudgetCertificate.certificateBudgetWindow ≤
      sampleUniformTailEnvelopesBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady
    (data : List UniformTailEnvelopesBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleUniformTailEnvelopesBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleUniformTailEnvelopesBudgetCertificate
  native_decide
end AnalyticCombinatorics.Asymptotics.UniformTailEnvelopes
