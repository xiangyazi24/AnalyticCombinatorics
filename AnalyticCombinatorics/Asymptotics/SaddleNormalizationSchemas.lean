import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Saddle normalization schemas.

The finite data records saddle width, normalization scale, and error
budget for normalized saddle estimates.
-/

namespace AnalyticCombinatorics.Asymptotics.SaddleNormalizationSchemas

structure SaddleNormalizationData where
  saddleWidth : ℕ
  normalizationScale : ℕ
  errorBudget : ℕ
deriving DecidableEq, Repr

def positiveNormalizationScale (d : SaddleNormalizationData) : Prop :=
  0 < d.normalizationScale

def saddleWidthControlled (d : SaddleNormalizationData) : Prop :=
  d.saddleWidth ≤ d.normalizationScale + d.errorBudget

def saddleNormalizationReady (d : SaddleNormalizationData) : Prop :=
  positiveNormalizationScale d ∧ saddleWidthControlled d

def saddleNormalizationBudget (d : SaddleNormalizationData) : ℕ :=
  d.saddleWidth + d.normalizationScale + d.errorBudget

theorem saddleNormalizationReady.scale {d : SaddleNormalizationData}
    (h : saddleNormalizationReady d) :
    positiveNormalizationScale d ∧ saddleWidthControlled d ∧
      d.saddleWidth ≤ saddleNormalizationBudget d := by
  refine ⟨h.1, h.2, ?_⟩
  unfold saddleNormalizationBudget
  omega

theorem saddleWidth_le_normalizationBudget
    (d : SaddleNormalizationData) :
    d.saddleWidth ≤ saddleNormalizationBudget d := by
  unfold saddleNormalizationBudget
  omega

def sampleSaddleNormalizationData : SaddleNormalizationData :=
  { saddleWidth := 7, normalizationScale := 5, errorBudget := 4 }

example : saddleNormalizationReady sampleSaddleNormalizationData := by
  norm_num [saddleNormalizationReady, positiveNormalizationScale]
  norm_num [saddleWidthControlled, sampleSaddleNormalizationData]

example : saddleNormalizationBudget sampleSaddleNormalizationData = 16 := by
  native_decide

/-- Finite executable readiness audit for saddle normalization data. -/
def saddleNormalizationDataListReady
    (data : List SaddleNormalizationData) : Bool :=
  data.all fun d =>
    0 < d.normalizationScale && d.saddleWidth ≤ d.normalizationScale + d.errorBudget

theorem saddleNormalizationDataList_readyWindow :
    saddleNormalizationDataListReady
      [{ saddleWidth := 4, normalizationScale := 3, errorBudget := 1 },
       { saddleWidth := 7, normalizationScale := 5, errorBudget := 4 }] = true := by
  unfold saddleNormalizationDataListReady
  native_decide

/-- A certificate window for saddle normalization schemas. -/
structure SaddleNormalizationCertificateWindow where
  saddleWindow : ℕ
  normalizationWindow : ℕ
  errorWindow : ℕ
  certificateBudget : ℕ
  slack : ℕ

/-- The saddle window is controlled by normalization and error windows. -/
def saddleNormalizationCertificateControlled
    (w : SaddleNormalizationCertificateWindow) : Prop :=
  w.saddleWindow ≤ w.normalizationWindow + w.errorWindow + w.slack

/-- Readiness for a saddle normalization certificate. -/
def saddleNormalizationCertificateReady
    (w : SaddleNormalizationCertificateWindow) : Prop :=
  0 < w.normalizationWindow ∧
    saddleNormalizationCertificateControlled w ∧
      w.certificateBudget ≤
        w.saddleWindow + w.normalizationWindow + w.errorWindow + w.slack

/-- Total size of a saddle normalization certificate. -/
def saddleNormalizationCertificate
    (w : SaddleNormalizationCertificateWindow) : ℕ :=
  w.saddleWindow + w.normalizationWindow + w.errorWindow +
    w.certificateBudget + w.slack

theorem saddleNormalizationCertificate_budget_le_certificate
    (w : SaddleNormalizationCertificateWindow)
    (h : saddleNormalizationCertificateReady w) :
    w.certificateBudget ≤ saddleNormalizationCertificate w := by
  rcases h with ⟨_, _, hbudget⟩
  unfold saddleNormalizationCertificate
  omega

def sampleSaddleNormalizationCertificateWindow :
    SaddleNormalizationCertificateWindow where
  saddleWindow := 7
  normalizationWindow := 6
  errorWindow := 2
  certificateBudget := 14
  slack := 1

example :
    saddleNormalizationCertificateReady
      sampleSaddleNormalizationCertificateWindow := by
  norm_num [saddleNormalizationCertificateReady,
    saddleNormalizationCertificateControlled,
    sampleSaddleNormalizationCertificateWindow]

example :
    sampleSaddleNormalizationCertificateWindow.certificateBudget ≤
      saddleNormalizationCertificate
        sampleSaddleNormalizationCertificateWindow := by
  apply saddleNormalizationCertificate_budget_le_certificate
  norm_num [saddleNormalizationCertificateReady,
    saddleNormalizationCertificateControlled,
    sampleSaddleNormalizationCertificateWindow]

structure SaddleNormalizationRefinementCertificate where
  saddleWindow : ℕ
  normalizationWindow : ℕ
  errorWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def SaddleNormalizationRefinementCertificate.saddleControlled
    (c : SaddleNormalizationRefinementCertificate) : Prop :=
  c.saddleWindow ≤ c.normalizationWindow + c.errorWindow + c.slack

def SaddleNormalizationRefinementCertificate.certificateBudgetControlled
    (c : SaddleNormalizationRefinementCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.saddleWindow + c.normalizationWindow + c.errorWindow + c.slack

def saddleNormalizationRefinementReady
    (c : SaddleNormalizationRefinementCertificate) : Prop :=
  0 < c.normalizationWindow ∧ c.saddleControlled ∧ c.certificateBudgetControlled

def SaddleNormalizationRefinementCertificate.size
    (c : SaddleNormalizationRefinementCertificate) : ℕ :=
  c.saddleWindow + c.normalizationWindow + c.errorWindow + c.slack

theorem saddleNormalization_certificateBudgetWindow_le_size
    {c : SaddleNormalizationRefinementCertificate}
    (h : saddleNormalizationRefinementReady c) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, _, hbudget⟩
  exact hbudget

def sampleSaddleNormalizationRefinementCertificate :
    SaddleNormalizationRefinementCertificate :=
  { saddleWindow := 7, normalizationWindow := 6, errorWindow := 2,
    certificateBudgetWindow := 16, slack := 1 }

example : saddleNormalizationRefinementReady
    sampleSaddleNormalizationRefinementCertificate := by
  norm_num [saddleNormalizationRefinementReady,
    SaddleNormalizationRefinementCertificate.saddleControlled,
    SaddleNormalizationRefinementCertificate.certificateBudgetControlled,
    sampleSaddleNormalizationRefinementCertificate]

example :
    sampleSaddleNormalizationRefinementCertificate.certificateBudgetWindow ≤
      sampleSaddleNormalizationRefinementCertificate.size := by
  norm_num [SaddleNormalizationRefinementCertificate.size,
    sampleSaddleNormalizationRefinementCertificate]

structure SaddleNormalizationBudgetCertificate where
  saddleWindow : ℕ
  normalizationWindow : ℕ
  errorWindow : ℕ
  normalizationBudgetWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def SaddleNormalizationBudgetCertificate.controlled
    (c : SaddleNormalizationBudgetCertificate) : Prop :=
  0 < c.normalizationWindow ∧
    c.saddleWindow ≤ c.normalizationWindow + c.errorWindow + c.slack ∧
      c.normalizationBudgetWindow ≤
        c.saddleWindow + c.normalizationWindow + c.errorWindow + c.slack

def SaddleNormalizationBudgetCertificate.budgetControlled
    (c : SaddleNormalizationBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.saddleWindow + c.normalizationWindow + c.errorWindow +
      c.normalizationBudgetWindow + c.slack

def SaddleNormalizationBudgetCertificate.Ready
    (c : SaddleNormalizationBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def SaddleNormalizationBudgetCertificate.size
    (c : SaddleNormalizationBudgetCertificate) : ℕ :=
  c.saddleWindow + c.normalizationWindow + c.errorWindow +
    c.normalizationBudgetWindow + c.slack

theorem saddleNormalization_budgetCertificate_le_size
    (c : SaddleNormalizationBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleSaddleNormalizationBudgetCertificate :
    SaddleNormalizationBudgetCertificate :=
  { saddleWindow := 7
    normalizationWindow := 6
    errorWindow := 2
    normalizationBudgetWindow := 16
    certificateBudgetWindow := 32
    slack := 1 }

example : sampleSaddleNormalizationBudgetCertificate.Ready := by
  constructor
  · norm_num [SaddleNormalizationBudgetCertificate.controlled,
      sampleSaddleNormalizationBudgetCertificate]
  · norm_num [SaddleNormalizationBudgetCertificate.budgetControlled,
      sampleSaddleNormalizationBudgetCertificate]

example :
    sampleSaddleNormalizationBudgetCertificate.certificateBudgetWindow ≤
      sampleSaddleNormalizationBudgetCertificate.size := by
  apply saddleNormalization_budgetCertificate_le_size
  constructor
  · norm_num [SaddleNormalizationBudgetCertificate.controlled,
      sampleSaddleNormalizationBudgetCertificate]
  · norm_num [SaddleNormalizationBudgetCertificate.budgetControlled,
      sampleSaddleNormalizationBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleSaddleNormalizationBudgetCertificate.Ready := by
  constructor
  · norm_num [SaddleNormalizationBudgetCertificate.controlled,
      sampleSaddleNormalizationBudgetCertificate]
  · norm_num [SaddleNormalizationBudgetCertificate.budgetControlled,
      sampleSaddleNormalizationBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleSaddleNormalizationBudgetCertificate.certificateBudgetWindow ≤
      sampleSaddleNormalizationBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady
    (data : List SaddleNormalizationBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleSaddleNormalizationBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleSaddleNormalizationBudgetCertificate
  native_decide
end AnalyticCombinatorics.Asymptotics.SaddleNormalizationSchemas
