import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Saddle error envelopes.

The finite record stores saddle scale, envelope height, and truncation
slack.
-/

namespace AnalyticCombinatorics.Asymptotics.SaddleErrorEnvelopes

structure SaddleErrorEnvelopeData where
  saddleScale : ℕ
  envelopeHeight : ℕ
  truncationSlack : ℕ
deriving DecidableEq, Repr

def saddleScalePositive (d : SaddleErrorEnvelopeData) : Prop :=
  0 < d.saddleScale

def envelopeControlled (d : SaddleErrorEnvelopeData) : Prop :=
  d.envelopeHeight ≤ d.saddleScale + d.truncationSlack

def saddleErrorEnvelopeReady (d : SaddleErrorEnvelopeData) : Prop :=
  saddleScalePositive d ∧ envelopeControlled d

def saddleErrorEnvelopeBudget (d : SaddleErrorEnvelopeData) : ℕ :=
  d.saddleScale + d.envelopeHeight + d.truncationSlack

theorem saddleErrorEnvelopeReady.scale {d : SaddleErrorEnvelopeData}
    (h : saddleErrorEnvelopeReady d) :
    saddleScalePositive d ∧ envelopeControlled d ∧
      d.envelopeHeight ≤ saddleErrorEnvelopeBudget d := by
  refine ⟨h.1, h.2, ?_⟩
  unfold saddleErrorEnvelopeBudget
  omega

theorem envelopeHeight_le_saddleEnvelopeBudget
    (d : SaddleErrorEnvelopeData) :
    d.envelopeHeight ≤ saddleErrorEnvelopeBudget d := by
  unfold saddleErrorEnvelopeBudget
  omega

def sampleSaddleErrorEnvelopeData : SaddleErrorEnvelopeData :=
  { saddleScale := 6, envelopeHeight := 8, truncationSlack := 3 }

example : saddleErrorEnvelopeReady sampleSaddleErrorEnvelopeData := by
  norm_num [saddleErrorEnvelopeReady, saddleScalePositive]
  norm_num [envelopeControlled, sampleSaddleErrorEnvelopeData]

example : saddleErrorEnvelopeBudget sampleSaddleErrorEnvelopeData = 17 := by
  native_decide

/-- Finite executable readiness audit for saddle error envelope data. -/
def saddleErrorEnvelopeDataListReady
    (data : List SaddleErrorEnvelopeData) : Bool :=
  data.all fun d =>
    0 < d.saddleScale && d.envelopeHeight ≤ d.saddleScale + d.truncationSlack

theorem saddleErrorEnvelopeDataList_readyWindow :
    saddleErrorEnvelopeDataListReady
      [{ saddleScale := 4, envelopeHeight := 5, truncationSlack := 1 },
       { saddleScale := 6, envelopeHeight := 8, truncationSlack := 3 }] = true := by
  unfold saddleErrorEnvelopeDataListReady
  native_decide

/-- A certificate window for saddle error envelopes. -/
structure SaddleErrorEnvelopeCertificateWindow where
  saddleWindow : ℕ
  envelopeWindow : ℕ
  truncationSlack : ℕ
  certificateBudget : ℕ
  slack : ℕ

/-- The envelope window is controlled by the saddle window. -/
def saddleErrorEnvelopeCertificateControlled
    (w : SaddleErrorEnvelopeCertificateWindow) : Prop :=
  w.envelopeWindow ≤ w.saddleWindow + w.truncationSlack + w.slack

/-- Readiness for a saddle error envelope certificate. -/
def saddleErrorEnvelopeCertificateReady
    (w : SaddleErrorEnvelopeCertificateWindow) : Prop :=
  0 < w.saddleWindow ∧
    saddleErrorEnvelopeCertificateControlled w ∧
      w.certificateBudget ≤ w.saddleWindow + w.envelopeWindow + w.slack

/-- Total size of a saddle error envelope certificate. -/
def saddleErrorEnvelopeCertificate
    (w : SaddleErrorEnvelopeCertificateWindow) : ℕ :=
  w.saddleWindow + w.envelopeWindow + w.truncationSlack +
    w.certificateBudget + w.slack

theorem saddleErrorEnvelopeCertificate_budget_le_certificate
    (w : SaddleErrorEnvelopeCertificateWindow)
    (h : saddleErrorEnvelopeCertificateReady w) :
    w.certificateBudget ≤ saddleErrorEnvelopeCertificate w := by
  rcases h with ⟨_, _, hbudget⟩
  unfold saddleErrorEnvelopeCertificate
  omega

def sampleSaddleErrorEnvelopeCertificateWindow :
    SaddleErrorEnvelopeCertificateWindow where
  saddleWindow := 6
  envelopeWindow := 7
  truncationSlack := 2
  certificateBudget := 12
  slack := 1

example :
    saddleErrorEnvelopeCertificateReady
      sampleSaddleErrorEnvelopeCertificateWindow := by
  norm_num [saddleErrorEnvelopeCertificateReady,
    saddleErrorEnvelopeCertificateControlled,
    sampleSaddleErrorEnvelopeCertificateWindow]

example :
    sampleSaddleErrorEnvelopeCertificateWindow.certificateBudget ≤
      saddleErrorEnvelopeCertificate
        sampleSaddleErrorEnvelopeCertificateWindow := by
  apply saddleErrorEnvelopeCertificate_budget_le_certificate
  norm_num [saddleErrorEnvelopeCertificateReady,
    saddleErrorEnvelopeCertificateControlled,
    sampleSaddleErrorEnvelopeCertificateWindow]

structure SaddleErrorEnvelopeRefinementCertificate where
  saddleWindow : ℕ
  envelopeWindow : ℕ
  truncationSlackWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def SaddleErrorEnvelopeRefinementCertificate.envelopeControlled
    (c : SaddleErrorEnvelopeRefinementCertificate) : Prop :=
  c.envelopeWindow ≤ c.saddleWindow + c.truncationSlackWindow + c.slack

def SaddleErrorEnvelopeRefinementCertificate.certificateBudgetControlled
    (c : SaddleErrorEnvelopeRefinementCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.saddleWindow + c.envelopeWindow + c.truncationSlackWindow + c.slack

def saddleErrorEnvelopeRefinementReady
    (c : SaddleErrorEnvelopeRefinementCertificate) : Prop :=
  0 < c.saddleWindow ∧ c.envelopeControlled ∧ c.certificateBudgetControlled

def SaddleErrorEnvelopeRefinementCertificate.size
    (c : SaddleErrorEnvelopeRefinementCertificate) : ℕ :=
  c.saddleWindow + c.envelopeWindow + c.truncationSlackWindow + c.slack

theorem saddleErrorEnvelope_certificateBudgetWindow_le_size
    {c : SaddleErrorEnvelopeRefinementCertificate}
    (h : saddleErrorEnvelopeRefinementReady c) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, _, hbudget⟩
  exact hbudget

def sampleSaddleErrorEnvelopeRefinementCertificate :
    SaddleErrorEnvelopeRefinementCertificate :=
  { saddleWindow := 6, envelopeWindow := 7, truncationSlackWindow := 2,
    certificateBudgetWindow := 16, slack := 1 }

example : saddleErrorEnvelopeRefinementReady
    sampleSaddleErrorEnvelopeRefinementCertificate := by
  norm_num [saddleErrorEnvelopeRefinementReady,
    SaddleErrorEnvelopeRefinementCertificate.envelopeControlled,
    SaddleErrorEnvelopeRefinementCertificate.certificateBudgetControlled,
    sampleSaddleErrorEnvelopeRefinementCertificate]

example :
    sampleSaddleErrorEnvelopeRefinementCertificate.certificateBudgetWindow ≤
      sampleSaddleErrorEnvelopeRefinementCertificate.size := by
  norm_num [SaddleErrorEnvelopeRefinementCertificate.size,
    sampleSaddleErrorEnvelopeRefinementCertificate]

structure SaddleErrorEnvelopeBudgetCertificate where
  saddleWindow : ℕ
  envelopeWindow : ℕ
  truncationSlackWindow : ℕ
  envelopeBudgetWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def SaddleErrorEnvelopeBudgetCertificate.controlled
    (c : SaddleErrorEnvelopeBudgetCertificate) : Prop :=
  0 < c.saddleWindow ∧
    c.envelopeWindow ≤ c.saddleWindow + c.truncationSlackWindow + c.slack ∧
      c.envelopeBudgetWindow ≤
        c.saddleWindow + c.envelopeWindow + c.truncationSlackWindow + c.slack

def SaddleErrorEnvelopeBudgetCertificate.budgetControlled
    (c : SaddleErrorEnvelopeBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.saddleWindow + c.envelopeWindow + c.truncationSlackWindow +
      c.envelopeBudgetWindow + c.slack

def SaddleErrorEnvelopeBudgetCertificate.Ready
    (c : SaddleErrorEnvelopeBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def SaddleErrorEnvelopeBudgetCertificate.size
    (c : SaddleErrorEnvelopeBudgetCertificate) : ℕ :=
  c.saddleWindow + c.envelopeWindow + c.truncationSlackWindow +
    c.envelopeBudgetWindow + c.slack

theorem saddleErrorEnvelope_budgetCertificate_le_size
    (c : SaddleErrorEnvelopeBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleSaddleErrorEnvelopeBudgetCertificate :
    SaddleErrorEnvelopeBudgetCertificate :=
  { saddleWindow := 6
    envelopeWindow := 7
    truncationSlackWindow := 2
    envelopeBudgetWindow := 16
    certificateBudgetWindow := 32
    slack := 1 }

example : sampleSaddleErrorEnvelopeBudgetCertificate.Ready := by
  constructor
  · norm_num [SaddleErrorEnvelopeBudgetCertificate.controlled,
      sampleSaddleErrorEnvelopeBudgetCertificate]
  · norm_num [SaddleErrorEnvelopeBudgetCertificate.budgetControlled,
      sampleSaddleErrorEnvelopeBudgetCertificate]

example :
    sampleSaddleErrorEnvelopeBudgetCertificate.certificateBudgetWindow ≤
      sampleSaddleErrorEnvelopeBudgetCertificate.size := by
  apply saddleErrorEnvelope_budgetCertificate_le_size
  constructor
  · norm_num [SaddleErrorEnvelopeBudgetCertificate.controlled,
      sampleSaddleErrorEnvelopeBudgetCertificate]
  · norm_num [SaddleErrorEnvelopeBudgetCertificate.budgetControlled,
      sampleSaddleErrorEnvelopeBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleSaddleErrorEnvelopeBudgetCertificate.Ready := by
  constructor
  · norm_num [SaddleErrorEnvelopeBudgetCertificate.controlled,
      sampleSaddleErrorEnvelopeBudgetCertificate]
  · norm_num [SaddleErrorEnvelopeBudgetCertificate.budgetControlled,
      sampleSaddleErrorEnvelopeBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleSaddleErrorEnvelopeBudgetCertificate.certificateBudgetWindow ≤
      sampleSaddleErrorEnvelopeBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady
    (data : List SaddleErrorEnvelopeBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleSaddleErrorEnvelopeBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleSaddleErrorEnvelopeBudgetCertificate
  native_decide
end AnalyticCombinatorics.Asymptotics.SaddleErrorEnvelopes
