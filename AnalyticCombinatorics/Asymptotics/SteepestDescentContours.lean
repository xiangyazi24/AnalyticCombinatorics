import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Steepest-descent contour bookkeeping.

The finite schema records local descent, tail suppression, and a positive
contour length.
-/

namespace AnalyticCombinatorics.Asymptotics.SteepestDescentContours

structure DescentContour where
  localLength : ℕ
  descentRate : ℕ
  tailSuppression : ℕ
deriving DecidableEq, Repr

def positiveLocalLength (c : DescentContour) : Prop :=
  0 < c.localLength

def descentSuppressesTail (c : DescentContour) : Prop :=
  c.tailSuppression ≤ c.descentRate

def steepestDescentReady (c : DescentContour) : Prop :=
  positiveLocalLength c ∧ descentSuppressesTail c

def contourComplexity (c : DescentContour) : ℕ :=
  c.localLength + c.descentRate + c.tailSuppression

theorem steepestDescentReady.descent {c : DescentContour}
    (h : steepestDescentReady c) :
    positiveLocalLength c ∧ descentSuppressesTail c ∧ c.localLength ≤ contourComplexity c := by
  refine ⟨h.1, h.2, ?_⟩
  unfold contourComplexity
  omega

theorem localLength_le_complexity (c : DescentContour) :
    c.localLength ≤ contourComplexity c := by
  unfold contourComplexity
  omega

def sampleDescentContour : DescentContour :=
  { localLength := 4, descentRate := 8, tailSuppression := 3 }

example : steepestDescentReady sampleDescentContour := by
  norm_num [steepestDescentReady, positiveLocalLength, descentSuppressesTail, sampleDescentContour]

example : contourComplexity sampleDescentContour = 15 := by
  native_decide

/-- Finite executable readiness audit for steepest descent contours. -/
def descentContourListReady (contours : List DescentContour) : Bool :=
  contours.all fun c => 0 < c.localLength && c.tailSuppression ≤ c.descentRate

theorem descentContourList_readyWindow :
    descentContourListReady
      [{ localLength := 2, descentRate := 4, tailSuppression := 1 },
       { localLength := 4, descentRate := 8, tailSuppression := 3 }] = true := by
  unfold descentContourListReady
  native_decide

structure SteepestDescentWindow where
  localLength : ℕ
  descentRate : ℕ
  tailSuppression : ℕ
  contourBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def SteepestDescentWindow.tailControlled (w : SteepestDescentWindow) : Prop :=
  w.tailSuppression ≤ w.descentRate + w.slack

def SteepestDescentWindow.contourControlled (w : SteepestDescentWindow) : Prop :=
  w.contourBudget ≤ w.localLength + w.descentRate + w.tailSuppression + w.slack

def steepestDescentWindowReady (w : SteepestDescentWindow) : Prop :=
  0 < w.localLength ∧
    w.tailControlled ∧
    w.contourControlled

def SteepestDescentWindow.certificate (w : SteepestDescentWindow) : ℕ :=
  w.localLength + w.descentRate + w.tailSuppression + w.slack

theorem steepestDescent_contourBudget_le_certificate {w : SteepestDescentWindow}
    (h : steepestDescentWindowReady w) :
    w.contourBudget ≤ w.certificate := by
  rcases h with ⟨_, _, hcontour⟩
  exact hcontour

def sampleSteepestDescentWindow : SteepestDescentWindow :=
  { localLength := 4, descentRate := 8, tailSuppression := 3, contourBudget := 14, slack := 0 }

example : steepestDescentWindowReady sampleSteepestDescentWindow := by
  norm_num [steepestDescentWindowReady, SteepestDescentWindow.tailControlled,
    SteepestDescentWindow.contourControlled, sampleSteepestDescentWindow]

example : sampleSteepestDescentWindow.certificate = 15 := by
  native_decide

/-- A refinement certificate for steepest-descent contour windows. -/
structure SteepestDescentCertificate where
  localLengthWindow : ℕ
  descentRateWindow : ℕ
  tailSuppressionWindow : ℕ
  contourBudgetWindow : ℕ
  slack : ℕ

/-- Tail suppression and contour budget are controlled by descent. -/
def steepestDescentCertificateControlled
    (w : SteepestDescentCertificate) : Prop :=
  0 < w.localLengthWindow ∧
    w.tailSuppressionWindow ≤ w.descentRateWindow + w.slack ∧
      w.contourBudgetWindow ≤
        w.localLengthWindow + w.descentRateWindow + w.tailSuppressionWindow + w.slack

/-- Readiness for a steepest-descent certificate. -/
def steepestDescentCertificateReady
    (w : SteepestDescentCertificate) : Prop :=
  steepestDescentCertificateControlled w ∧
    w.contourBudgetWindow ≤
      w.localLengthWindow + w.descentRateWindow + w.tailSuppressionWindow +
        w.contourBudgetWindow + w.slack

/-- Total size of a steepest-descent certificate. -/
def steepestDescentCertificateSize
    (w : SteepestDescentCertificate) : ℕ :=
  w.localLengthWindow + w.descentRateWindow + w.tailSuppressionWindow +
    w.contourBudgetWindow + w.slack

theorem steepestDescentCertificate_budget_le_size
    (w : SteepestDescentCertificate)
    (h : steepestDescentCertificateReady w) :
    w.contourBudgetWindow ≤ steepestDescentCertificateSize w := by
  rcases h with ⟨_, hbudget⟩
  unfold steepestDescentCertificateSize
  omega

def sampleSteepestDescentCertificate : SteepestDescentCertificate where
  localLengthWindow := 4
  descentRateWindow := 8
  tailSuppressionWindow := 3
  contourBudgetWindow := 14
  slack := 0

example :
    steepestDescentCertificateReady sampleSteepestDescentCertificate := by
  norm_num [steepestDescentCertificateReady,
    steepestDescentCertificateControlled, sampleSteepestDescentCertificate]

example :
    sampleSteepestDescentCertificate.contourBudgetWindow ≤
      steepestDescentCertificateSize sampleSteepestDescentCertificate := by
  apply steepestDescentCertificate_budget_le_size
  norm_num [steepestDescentCertificateReady,
    steepestDescentCertificateControlled, sampleSteepestDescentCertificate]

/-- A refinement certificate with the steepest-descent budget separated from size. -/
structure SteepestDescentRefinementCertificate where
  localLengthWindow : ℕ
  descentRateWindow : ℕ
  tailSuppressionWindow : ℕ
  contourBudgetWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def SteepestDescentRefinementCertificate.contourControlled
    (cert : SteepestDescentRefinementCertificate) : Prop :=
  0 < cert.localLengthWindow ∧
    cert.tailSuppressionWindow ≤ cert.descentRateWindow + cert.slack ∧
      cert.contourBudgetWindow ≤
        cert.localLengthWindow + cert.descentRateWindow + cert.tailSuppressionWindow + cert.slack

def SteepestDescentRefinementCertificate.budgetControlled
    (cert : SteepestDescentRefinementCertificate) : Prop :=
  cert.certificateBudgetWindow ≤
    cert.localLengthWindow + cert.descentRateWindow + cert.tailSuppressionWindow +
      cert.contourBudgetWindow + cert.slack

def steepestDescentRefinementReady
    (cert : SteepestDescentRefinementCertificate) : Prop :=
  cert.contourControlled ∧ cert.budgetControlled

def SteepestDescentRefinementCertificate.size
    (cert : SteepestDescentRefinementCertificate) : ℕ :=
  cert.localLengthWindow + cert.descentRateWindow + cert.tailSuppressionWindow +
    cert.contourBudgetWindow + cert.slack

theorem steepestDescent_certificateBudgetWindow_le_size
    (cert : SteepestDescentRefinementCertificate)
    (h : steepestDescentRefinementReady cert) :
    cert.certificateBudgetWindow ≤ cert.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleSteepestDescentRefinementCertificate :
    SteepestDescentRefinementCertificate :=
  { localLengthWindow := 4, descentRateWindow := 8, tailSuppressionWindow := 3,
    contourBudgetWindow := 14, certificateBudgetWindow := 29, slack := 0 }

example :
    steepestDescentRefinementReady sampleSteepestDescentRefinementCertificate := by
  norm_num [steepestDescentRefinementReady,
    SteepestDescentRefinementCertificate.contourControlled,
    SteepestDescentRefinementCertificate.budgetControlled,
    sampleSteepestDescentRefinementCertificate]

example :
    sampleSteepestDescentRefinementCertificate.certificateBudgetWindow ≤
      sampleSteepestDescentRefinementCertificate.size := by
  apply steepestDescent_certificateBudgetWindow_le_size
  norm_num [steepestDescentRefinementReady,
    SteepestDescentRefinementCertificate.contourControlled,
    SteepestDescentRefinementCertificate.budgetControlled,
    sampleSteepestDescentRefinementCertificate]


structure SteepestDescentContoursBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def SteepestDescentContoursBudgetCertificate.controlled
    (c : SteepestDescentContoursBudgetCertificate) : Prop :=
  0 < c.primaryWindow ∧ c.secondaryWindow ≤ c.primaryWindow + c.slack

def SteepestDescentContoursBudgetCertificate.budgetControlled
    (c : SteepestDescentContoursBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def SteepestDescentContoursBudgetCertificate.Ready
    (c : SteepestDescentContoursBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def SteepestDescentContoursBudgetCertificate.size
    (c : SteepestDescentContoursBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem steepestDescentContours_budgetCertificate_le_size
    (c : SteepestDescentContoursBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleSteepestDescentContoursBudgetCertificate :
    SteepestDescentContoursBudgetCertificate :=
  { primaryWindow := 5
    secondaryWindow := 6
    certificateBudgetWindow := 12
    slack := 1 }

example : sampleSteepestDescentContoursBudgetCertificate.Ready := by
  constructor
  · norm_num [SteepestDescentContoursBudgetCertificate.controlled,
      sampleSteepestDescentContoursBudgetCertificate]
  · norm_num [SteepestDescentContoursBudgetCertificate.budgetControlled,
      sampleSteepestDescentContoursBudgetCertificate]

example :
    sampleSteepestDescentContoursBudgetCertificate.certificateBudgetWindow ≤
      sampleSteepestDescentContoursBudgetCertificate.size := by
  apply steepestDescentContours_budgetCertificate_le_size
  constructor
  · norm_num [SteepestDescentContoursBudgetCertificate.controlled,
      sampleSteepestDescentContoursBudgetCertificate]
  · norm_num [SteepestDescentContoursBudgetCertificate.budgetControlled,
      sampleSteepestDescentContoursBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleSteepestDescentContoursBudgetCertificate.Ready := by
  constructor
  · norm_num [SteepestDescentContoursBudgetCertificate.controlled,
      sampleSteepestDescentContoursBudgetCertificate]
  · norm_num [SteepestDescentContoursBudgetCertificate.budgetControlled,
      sampleSteepestDescentContoursBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleSteepestDescentContoursBudgetCertificate.certificateBudgetWindow ≤
      sampleSteepestDescentContoursBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady
    (data : List SteepestDescentContoursBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleSteepestDescentContoursBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleSteepestDescentContoursBudgetCertificate
  native_decide
end AnalyticCombinatorics.Asymptotics.SteepestDescentContours
