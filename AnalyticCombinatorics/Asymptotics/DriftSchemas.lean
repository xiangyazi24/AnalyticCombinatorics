import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Drift and variance bookkeeping for asymptotic regimes.

The schemas here are finite versions of the positivity and centering checks
used before local and global limit estimates.
-/

namespace AnalyticCombinatorics.Asymptotics.DriftSchemas

structure DriftData where
  drift : ℤ
  variance : ℕ
  centeringError : ℕ
deriving DecidableEq, Repr

def positiveVariance (d : DriftData) : Prop :=
  0 < d.variance

def centeredWithin (d : DriftData) (budget : ℕ) : Prop :=
  d.centeringError ≤ budget

def driftReady (d : DriftData) (budget : ℕ) : Prop :=
  positiveVariance d ∧ centeredWithin d budget

def absoluteDriftBudget (d : DriftData) : ℕ :=
  d.drift.natAbs + d.centeringError

theorem driftReady.variance {d : DriftData} {budget : ℕ}
    (h : driftReady d budget) :
    positiveVariance d ∧ centeredWithin d budget := ⟨h.1, h.2⟩

theorem centeredWithin_mono {d : DriftData} {b c : ℕ}
    (h : centeredWithin d b) (hbc : b ≤ c) :
    centeredWithin d c := by
  unfold centeredWithin at *
  omega

def sampleDrift : DriftData :=
  { drift := -3, variance := 5, centeringError := 2 }

example : driftReady sampleDrift 4 := by
  norm_num [driftReady, positiveVariance, centeredWithin, sampleDrift]

example : absoluteDriftBudget sampleDrift = 5 := by
  native_decide

structure DriftWindow where
  driftMagnitude : ℕ
  variance : ℕ
  centeringError : ℕ
  scaleBudget : ℕ
deriving DecidableEq, Repr

def DriftWindow.varianceReady (w : DriftWindow) : Prop :=
  0 < w.variance

def DriftWindow.centeringControlled (w : DriftWindow) : Prop :=
  w.centeringError ≤ w.scaleBudget

def DriftWindow.driftControlled (w : DriftWindow) : Prop :=
  w.driftMagnitude ≤ w.scaleBudget + w.variance

def DriftWindow.ready (w : DriftWindow) : Prop :=
  w.varianceReady ∧ w.centeringControlled ∧ w.driftControlled

def DriftWindow.certificate (w : DriftWindow) : ℕ :=
  w.driftMagnitude + w.variance + w.centeringError + w.scaleBudget

theorem driftMagnitude_le_certificate (w : DriftWindow) :
    w.driftMagnitude ≤ w.certificate := by
  unfold DriftWindow.certificate
  omega

def sampleDriftWindow : DriftWindow :=
  { driftMagnitude := 3, variance := 5, centeringError := 2, scaleBudget := 4 }

example : sampleDriftWindow.ready := by
  norm_num [sampleDriftWindow, DriftWindow.ready, DriftWindow.varianceReady,
    DriftWindow.centeringControlled, DriftWindow.driftControlled]

/-- Finite executable readiness audit for drift windows. -/
def driftWindowListReady (windows : List DriftWindow) : Bool :=
  windows.all fun w =>
    0 < w.variance &&
      w.centeringError ≤ w.scaleBudget &&
        w.driftMagnitude ≤ w.scaleBudget + w.variance

theorem driftWindowList_readyWindow :
    driftWindowListReady
      [{ driftMagnitude := 2, variance := 3, centeringError := 1, scaleBudget := 2 },
       { driftMagnitude := 3, variance := 5, centeringError := 2, scaleBudget := 4 }] =
      true := by
  unfold driftWindowListReady
  native_decide

/-- A refinement certificate for drift and centering windows. -/
structure DriftCertificate where
  driftWindow : ℕ
  varianceWindow : ℕ
  centeringWindow : ℕ
  scaleWindow : ℕ
  slack : ℕ

/-- Variance is positive and drift/centering are controlled by the scale. -/
def driftCertificateControlled
    (w : DriftCertificate) : Prop :=
  0 < w.varianceWindow ∧
    w.centeringWindow ≤ w.scaleWindow + w.slack ∧
      w.driftWindow ≤ w.scaleWindow + w.varianceWindow + w.slack

/-- Readiness for a drift certificate. -/
def driftCertificateReady
    (w : DriftCertificate) : Prop :=
  driftCertificateControlled w ∧
    w.driftWindow ≤ w.driftWindow + w.varianceWindow + w.centeringWindow + w.scaleWindow + w.slack

/-- Total size of a drift certificate. -/
def driftCertificateSize (w : DriftCertificate) : ℕ :=
  w.driftWindow + w.varianceWindow + w.centeringWindow + w.scaleWindow + w.slack

theorem driftCertificate_drift_le_size
    (w : DriftCertificate)
    (h : driftCertificateReady w) :
    w.driftWindow ≤ driftCertificateSize w := by
  rcases h with ⟨_, hbudget⟩
  unfold driftCertificateSize
  omega

def sampleDriftCertificate : DriftCertificate where
  driftWindow := 3
  varianceWindow := 5
  centeringWindow := 2
  scaleWindow := 4
  slack := 0

example :
    driftCertificateReady sampleDriftCertificate := by
  norm_num [driftCertificateReady,
    driftCertificateControlled, sampleDriftCertificate]

example :
    sampleDriftCertificate.driftWindow ≤
      driftCertificateSize sampleDriftCertificate := by
  apply driftCertificate_drift_le_size
  norm_num [driftCertificateReady,
    driftCertificateControlled, sampleDriftCertificate]

/-- A refinement certificate with the drift bookkeeping budget separated from size. -/
structure DriftRefinementCertificate where
  driftWindow : ℕ
  varianceWindow : ℕ
  centeringWindow : ℕ
  scaleWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ

def DriftRefinementCertificate.driftControlled
    (cert : DriftRefinementCertificate) : Prop :=
  0 < cert.varianceWindow ∧
    cert.centeringWindow ≤ cert.scaleWindow + cert.slack ∧
      cert.driftWindow ≤ cert.scaleWindow + cert.varianceWindow + cert.slack

def DriftRefinementCertificate.budgetControlled
    (cert : DriftRefinementCertificate) : Prop :=
  cert.certificateBudgetWindow ≤
    cert.driftWindow + cert.varianceWindow + cert.centeringWindow +
      cert.scaleWindow + cert.slack

def driftRefinementReady (cert : DriftRefinementCertificate) : Prop :=
  cert.driftControlled ∧ cert.budgetControlled

def DriftRefinementCertificate.size
    (cert : DriftRefinementCertificate) : ℕ :=
  cert.driftWindow + cert.varianceWindow + cert.centeringWindow +
    cert.scaleWindow + cert.slack

theorem drift_certificateBudgetWindow_le_size
    (cert : DriftRefinementCertificate)
    (h : driftRefinementReady cert) :
    cert.certificateBudgetWindow ≤ cert.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleDriftRefinementCertificate : DriftRefinementCertificate where
  driftWindow := 3
  varianceWindow := 5
  centeringWindow := 2
  scaleWindow := 4
  certificateBudgetWindow := 14
  slack := 0

example : driftRefinementReady sampleDriftRefinementCertificate := by
  norm_num [driftRefinementReady, DriftRefinementCertificate.driftControlled,
    DriftRefinementCertificate.budgetControlled, sampleDriftRefinementCertificate]

example :
    sampleDriftRefinementCertificate.certificateBudgetWindow ≤
      sampleDriftRefinementCertificate.size := by
  apply drift_certificateBudgetWindow_le_size
  norm_num [driftRefinementReady, DriftRefinementCertificate.driftControlled,
    DriftRefinementCertificate.budgetControlled, sampleDriftRefinementCertificate]


structure DriftSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def DriftSchemasBudgetCertificate.controlled
    (c : DriftSchemasBudgetCertificate) : Prop :=
  0 < c.primaryWindow ∧ c.secondaryWindow ≤ c.primaryWindow + c.slack

def DriftSchemasBudgetCertificate.budgetControlled
    (c : DriftSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def DriftSchemasBudgetCertificate.Ready
    (c : DriftSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def DriftSchemasBudgetCertificate.size
    (c : DriftSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem driftSchemas_budgetCertificate_le_size
    (c : DriftSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleDriftSchemasBudgetCertificate :
    DriftSchemasBudgetCertificate :=
  { primaryWindow := 5
    secondaryWindow := 6
    certificateBudgetWindow := 12
    slack := 1 }

example : sampleDriftSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [DriftSchemasBudgetCertificate.controlled,
      sampleDriftSchemasBudgetCertificate]
  · norm_num [DriftSchemasBudgetCertificate.budgetControlled,
      sampleDriftSchemasBudgetCertificate]

example :
    sampleDriftSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleDriftSchemasBudgetCertificate.size := by
  apply driftSchemas_budgetCertificate_le_size
  constructor
  · norm_num [DriftSchemasBudgetCertificate.controlled,
      sampleDriftSchemasBudgetCertificate]
  · norm_num [DriftSchemasBudgetCertificate.budgetControlled,
      sampleDriftSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleDriftSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [DriftSchemasBudgetCertificate.controlled,
      sampleDriftSchemasBudgetCertificate]
  · norm_num [DriftSchemasBudgetCertificate.budgetControlled,
      sampleDriftSchemasBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleDriftSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleDriftSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady
    (data : List DriftSchemasBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleDriftSchemasBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleDriftSchemasBudgetCertificate
  native_decide
end AnalyticCombinatorics.Asymptotics.DriftSchemas
