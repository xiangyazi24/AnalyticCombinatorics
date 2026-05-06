import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Uniform error-envelope bookkeeping.

The definitions model how a pointwise error budget is dominated by a common
envelope across a finite range of parameters.
-/

namespace AnalyticCombinatorics.Asymptotics.UniformErrorEnvelopes

def envelopeDominates (error envelope : ℕ → ℕ) : Prop :=
  ∀ n, error n ≤ envelope n

def envelopeMass (envelope : ℕ → ℕ) (N : ℕ) : ℕ :=
  (List.range (N + 1)).map envelope |>.sum

def zeroError (n : ℕ) : ℕ := n - n

theorem zeroError_dominated (envelope : ℕ → ℕ) :
    envelopeDominates zeroError envelope := by
  intro n
  simp [zeroError]

theorem envelopeDominates_mono {error envelope larger : ℕ → ℕ}
    (h : envelopeDominates error envelope)
    (hl : envelopeDominates envelope larger) :
    envelopeDominates error larger := by
  intro n
  exact le_trans (h n) (hl n)

def sampleEnvelope : ℕ → ℕ
  | 0 => 1
  | 1 => 2
  | _ => 3

example : envelopeMass sampleEnvelope 2 = 6 := by
  native_decide

example : envelopeDominates zeroError sampleEnvelope := by
  exact zeroError_dominated sampleEnvelope

structure UniformErrorWindow where
  cutoff : ℕ
  pointwiseError : ℕ
  envelopeBound : ℕ
  accumulatedError : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def UniformErrorWindow.pointwiseReady (w : UniformErrorWindow) : Prop :=
  w.pointwiseError ≤ w.envelopeBound + w.slack

def UniformErrorWindow.accumulatedReady (w : UniformErrorWindow) : Prop :=
  w.accumulatedError ≤ (w.cutoff + 1) * w.envelopeBound + w.slack

def UniformErrorWindow.ready (w : UniformErrorWindow) : Prop :=
  w.pointwiseReady ∧ w.accumulatedReady

def UniformErrorWindow.certificate (w : UniformErrorWindow) : ℕ :=
  w.cutoff + w.pointwiseError + w.envelopeBound + w.accumulatedError + w.slack

theorem accumulatedError_le_certificate (w : UniformErrorWindow) :
    w.accumulatedError ≤ w.certificate := by
  unfold UniformErrorWindow.certificate
  omega

def sampleUniformErrorWindow : UniformErrorWindow :=
  { cutoff := 2, pointwiseError := 3, envelopeBound := 3, accumulatedError := 6, slack := 0 }

example : sampleUniformErrorWindow.ready := by
  norm_num [sampleUniformErrorWindow, UniformErrorWindow.ready,
    UniformErrorWindow.pointwiseReady, UniformErrorWindow.accumulatedReady]

/-- Finite executable readiness audit for uniform error windows. -/
def uniformErrorWindowListReady (data : List UniformErrorWindow) : Bool :=
  data.all fun w =>
    w.pointwiseError ≤ w.envelopeBound + w.slack &&
      w.accumulatedError ≤ (w.cutoff + 1) * w.envelopeBound + w.slack

theorem uniformErrorWindowList_readyWindow :
    uniformErrorWindowListReady
      [{ cutoff := 2, pointwiseError := 3, envelopeBound := 3,
         accumulatedError := 6, slack := 0 },
       { cutoff := 3, pointwiseError := 5, envelopeBound := 4,
         accumulatedError := 13, slack := 1 }] = true := by
  unfold uniformErrorWindowListReady
  native_decide

/-- A refinement certificate for uniform error envelopes. -/
structure UniformErrorEnvelopeCertificate where
  cutoffWindow : ℕ
  pointwiseWindow : ℕ
  envelopeWindow : ℕ
  accumulatedWindow : ℕ
  slack : ℕ

/-- Accumulated and pointwise errors are controlled by a common envelope. -/
def uniformErrorEnvelopeCertificateControlled
    (w : UniformErrorEnvelopeCertificate) : Prop :=
  w.pointwiseWindow ≤ w.envelopeWindow + w.slack ∧
    w.accumulatedWindow ≤ (w.cutoffWindow + 1) * w.envelopeWindow + w.slack

/-- Readiness for a uniform error envelope certificate. -/
def uniformErrorEnvelopeCertificateReady
    (w : UniformErrorEnvelopeCertificate) : Prop :=
  uniformErrorEnvelopeCertificateControlled w ∧
    w.accumulatedWindow ≤ w.cutoffWindow + w.envelopeWindow + w.accumulatedWindow + w.slack

/-- Total size of a uniform error envelope certificate. -/
def uniformErrorEnvelopeCertificateSize
    (w : UniformErrorEnvelopeCertificate) : ℕ :=
  w.cutoffWindow + w.pointwiseWindow + w.envelopeWindow +
    w.accumulatedWindow + w.slack

theorem uniformErrorEnvelopeCertificate_accumulated_le_size
    (w : UniformErrorEnvelopeCertificate)
    (h : uniformErrorEnvelopeCertificateReady w) :
    w.accumulatedWindow ≤ uniformErrorEnvelopeCertificateSize w := by
  rcases h with ⟨_, hbudget⟩
  unfold uniformErrorEnvelopeCertificateSize
  omega

def sampleUniformErrorEnvelopeCertificate :
    UniformErrorEnvelopeCertificate where
  cutoffWindow := 2
  pointwiseWindow := 3
  envelopeWindow := 3
  accumulatedWindow := 6
  slack := 0

example :
    uniformErrorEnvelopeCertificateReady
      sampleUniformErrorEnvelopeCertificate := by
  norm_num [uniformErrorEnvelopeCertificateReady,
    uniformErrorEnvelopeCertificateControlled,
    sampleUniformErrorEnvelopeCertificate]

example :
    sampleUniformErrorEnvelopeCertificate.accumulatedWindow ≤
      uniformErrorEnvelopeCertificateSize
        sampleUniformErrorEnvelopeCertificate := by
  apply uniformErrorEnvelopeCertificate_accumulated_le_size
  norm_num [uniformErrorEnvelopeCertificateReady,
    uniformErrorEnvelopeCertificateControlled,
    sampleUniformErrorEnvelopeCertificate]

/-- A refinement certificate with the accumulated-error budget separated from size. -/
structure UniformErrorEnvelopeRefinementCertificate where
  cutoffWindow : ℕ
  pointwiseWindow : ℕ
  envelopeWindow : ℕ
  accumulatedWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ

def UniformErrorEnvelopeRefinementCertificate.errorControlled
    (cert : UniformErrorEnvelopeRefinementCertificate) : Prop :=
  cert.pointwiseWindow ≤ cert.envelopeWindow + cert.slack ∧
    cert.accumulatedWindow ≤ (cert.cutoffWindow + 1) * cert.envelopeWindow + cert.slack

def UniformErrorEnvelopeRefinementCertificate.budgetControlled
    (cert : UniformErrorEnvelopeRefinementCertificate) : Prop :=
  cert.certificateBudgetWindow ≤
    cert.cutoffWindow + cert.pointwiseWindow + cert.envelopeWindow +
      cert.accumulatedWindow + cert.slack

def uniformErrorEnvelopeRefinementReady
    (cert : UniformErrorEnvelopeRefinementCertificate) : Prop :=
  cert.errorControlled ∧ cert.budgetControlled

def UniformErrorEnvelopeRefinementCertificate.size
    (cert : UniformErrorEnvelopeRefinementCertificate) : ℕ :=
  cert.cutoffWindow + cert.pointwiseWindow + cert.envelopeWindow +
    cert.accumulatedWindow + cert.slack

theorem uniformErrorEnvelope_certificateBudgetWindow_le_size
    (cert : UniformErrorEnvelopeRefinementCertificate)
    (h : uniformErrorEnvelopeRefinementReady cert) :
    cert.certificateBudgetWindow ≤ cert.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleUniformErrorEnvelopeRefinementCertificate :
    UniformErrorEnvelopeRefinementCertificate where
  cutoffWindow := 2
  pointwiseWindow := 3
  envelopeWindow := 3
  accumulatedWindow := 6
  certificateBudgetWindow := 14
  slack := 0

example :
    uniformErrorEnvelopeRefinementReady
      sampleUniformErrorEnvelopeRefinementCertificate := by
  norm_num [uniformErrorEnvelopeRefinementReady,
    UniformErrorEnvelopeRefinementCertificate.errorControlled,
    UniformErrorEnvelopeRefinementCertificate.budgetControlled,
    sampleUniformErrorEnvelopeRefinementCertificate]

example :
    sampleUniformErrorEnvelopeRefinementCertificate.certificateBudgetWindow ≤
      sampleUniformErrorEnvelopeRefinementCertificate.size := by
  apply uniformErrorEnvelope_certificateBudgetWindow_le_size
  norm_num [uniformErrorEnvelopeRefinementReady,
    UniformErrorEnvelopeRefinementCertificate.errorControlled,
    UniformErrorEnvelopeRefinementCertificate.budgetControlled,
    sampleUniformErrorEnvelopeRefinementCertificate]


structure UniformErrorEnvelopesBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def UniformErrorEnvelopesBudgetCertificate.controlled
    (c : UniformErrorEnvelopesBudgetCertificate) : Prop :=
  0 < c.primaryWindow ∧ c.secondaryWindow ≤ c.primaryWindow + c.slack

def UniformErrorEnvelopesBudgetCertificate.budgetControlled
    (c : UniformErrorEnvelopesBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def UniformErrorEnvelopesBudgetCertificate.Ready
    (c : UniformErrorEnvelopesBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def UniformErrorEnvelopesBudgetCertificate.size
    (c : UniformErrorEnvelopesBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem uniformErrorEnvelopes_budgetCertificate_le_size
    (c : UniformErrorEnvelopesBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleUniformErrorEnvelopesBudgetCertificate :
    UniformErrorEnvelopesBudgetCertificate :=
  { primaryWindow := 5
    secondaryWindow := 6
    certificateBudgetWindow := 12
    slack := 1 }

example : sampleUniformErrorEnvelopesBudgetCertificate.Ready := by
  constructor
  · norm_num [UniformErrorEnvelopesBudgetCertificate.controlled,
      sampleUniformErrorEnvelopesBudgetCertificate]
  · norm_num [UniformErrorEnvelopesBudgetCertificate.budgetControlled,
      sampleUniformErrorEnvelopesBudgetCertificate]

example :
    sampleUniformErrorEnvelopesBudgetCertificate.certificateBudgetWindow ≤
      sampleUniformErrorEnvelopesBudgetCertificate.size := by
  apply uniformErrorEnvelopes_budgetCertificate_le_size
  constructor
  · norm_num [UniformErrorEnvelopesBudgetCertificate.controlled,
      sampleUniformErrorEnvelopesBudgetCertificate]
  · norm_num [UniformErrorEnvelopesBudgetCertificate.budgetControlled,
      sampleUniformErrorEnvelopesBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleUniformErrorEnvelopesBudgetCertificate.Ready := by
  constructor
  · norm_num [UniformErrorEnvelopesBudgetCertificate.controlled,
      sampleUniformErrorEnvelopesBudgetCertificate]
  · norm_num [UniformErrorEnvelopesBudgetCertificate.budgetControlled,
      sampleUniformErrorEnvelopesBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleUniformErrorEnvelopesBudgetCertificate.certificateBudgetWindow ≤
      sampleUniformErrorEnvelopesBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady
    (data : List UniformErrorEnvelopesBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleUniformErrorEnvelopesBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleUniformErrorEnvelopesBudgetCertificate
  native_decide
end AnalyticCombinatorics.Asymptotics.UniformErrorEnvelopes
