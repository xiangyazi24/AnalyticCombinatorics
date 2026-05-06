import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Coefficient smoothing windows.

This module records finite bookkeeping for coefficient smoothing windows.
-/

namespace AnalyticCombinatorics.Asymptotics.CoefficientSmoothingWindows

structure CoefficientSmoothingData where
  smoothingRadius : ℕ
  coefficientRange : ℕ
  smoothingSlack : ℕ
deriving DecidableEq, Repr

def hasSmoothingRadius (d : CoefficientSmoothingData) : Prop :=
  0 < d.smoothingRadius

def coefficientRangeControlled (d : CoefficientSmoothingData) : Prop :=
  d.coefficientRange ≤ d.smoothingRadius + d.smoothingSlack

def coefficientSmoothingReady (d : CoefficientSmoothingData) : Prop :=
  hasSmoothingRadius d ∧ coefficientRangeControlled d

def coefficientSmoothingBudget (d : CoefficientSmoothingData) : ℕ :=
  d.smoothingRadius + d.coefficientRange + d.smoothingSlack

theorem coefficientSmoothingReady.hasSmoothingRadius
    {d : CoefficientSmoothingData}
    (h : coefficientSmoothingReady d) :
    hasSmoothingRadius d ∧ coefficientRangeControlled d ∧
      d.coefficientRange ≤ coefficientSmoothingBudget d := by
  refine ⟨h.1, h.2, ?_⟩
  unfold coefficientSmoothingBudget
  omega

theorem coefficientRange_le_budget (d : CoefficientSmoothingData) :
    d.coefficientRange ≤ coefficientSmoothingBudget d := by
  unfold coefficientSmoothingBudget
  omega

def sampleCoefficientSmoothingData : CoefficientSmoothingData :=
  { smoothingRadius := 6, coefficientRange := 8, smoothingSlack := 3 }

example : coefficientSmoothingReady sampleCoefficientSmoothingData := by
  norm_num [coefficientSmoothingReady, hasSmoothingRadius]
  norm_num [coefficientRangeControlled, sampleCoefficientSmoothingData]

example : coefficientSmoothingBudget sampleCoefficientSmoothingData = 17 := by
  native_decide

/-- Finite executable readiness audit for coefficient smoothing windows. -/
def coefficientSmoothingListReady
    (windows : List CoefficientSmoothingData) : Bool :=
  windows.all fun d =>
    0 < d.smoothingRadius &&
      d.coefficientRange ≤ d.smoothingRadius + d.smoothingSlack

theorem coefficientSmoothingList_readyWindow :
    coefficientSmoothingListReady
      [{ smoothingRadius := 4, coefficientRange := 5, smoothingSlack := 1 },
       { smoothingRadius := 6, coefficientRange := 8, smoothingSlack := 3 }] =
      true := by
  unfold coefficientSmoothingListReady
  native_decide

/-- A certified window for smoothing coefficient estimates. -/
structure CoefficientSmoothingCertificateWindow where
  radiusWindow : ℕ
  rangeWindow : ℕ
  smoothingSlack : ℕ
  smoothingBudget : ℕ
  slack : ℕ

/-- The range window is controlled by the smoothing radius. -/
def coefficientSmoothingCertificateControlled
    (w : CoefficientSmoothingCertificateWindow) : Prop :=
  w.rangeWindow ≤ w.radiusWindow + w.smoothingSlack + w.slack

/-- Readiness predicate for the smoothing certificate. -/
def coefficientSmoothingCertificateReady
    (w : CoefficientSmoothingCertificateWindow) : Prop :=
  0 < w.radiusWindow ∧
    coefficientSmoothingCertificateControlled w ∧
      w.smoothingBudget ≤ w.radiusWindow + w.rangeWindow + w.slack

/-- Total certificate size for smoothing coefficients. -/
def coefficientSmoothingCertificate
    (w : CoefficientSmoothingCertificateWindow) : ℕ :=
  w.radiusWindow + w.rangeWindow + w.smoothingSlack + w.smoothingBudget + w.slack

theorem coefficientSmoothingCertificate_budget_le_certificate
    (w : CoefficientSmoothingCertificateWindow)
    (h : coefficientSmoothingCertificateReady w) :
    w.smoothingBudget ≤ coefficientSmoothingCertificate w := by
  rcases h with ⟨_, _, hbudget⟩
  unfold coefficientSmoothingCertificate
  omega

def sampleCoefficientSmoothingCertificateWindow :
    CoefficientSmoothingCertificateWindow where
  radiusWindow := 5
  rangeWindow := 6
  smoothingSlack := 2
  smoothingBudget := 10
  slack := 1

example :
    coefficientSmoothingCertificateReady
      sampleCoefficientSmoothingCertificateWindow := by
  norm_num [coefficientSmoothingCertificateReady,
    coefficientSmoothingCertificateControlled,
    sampleCoefficientSmoothingCertificateWindow]

example :
    sampleCoefficientSmoothingCertificateWindow.smoothingBudget ≤
      coefficientSmoothingCertificate
        sampleCoefficientSmoothingCertificateWindow := by
  apply coefficientSmoothingCertificate_budget_le_certificate
  norm_num [coefficientSmoothingCertificateReady,
    coefficientSmoothingCertificateControlled,
    sampleCoefficientSmoothingCertificateWindow]

structure CoefficientSmoothingRefinementCertificate where
  radiusWindow : ℕ
  rangeWindow : ℕ
  smoothingSlackWindow : ℕ
  smoothingBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def CoefficientSmoothingRefinementCertificate.rangeControlled
    (c : CoefficientSmoothingRefinementCertificate) : Prop :=
  c.rangeWindow ≤ c.radiusWindow + c.smoothingSlackWindow + c.slack

def CoefficientSmoothingRefinementCertificate.smoothingBudgetControlled
    (c : CoefficientSmoothingRefinementCertificate) : Prop :=
  c.smoothingBudgetWindow ≤
    c.radiusWindow + c.rangeWindow + c.smoothingSlackWindow + c.slack

def coefficientSmoothingRefinementReady
    (c : CoefficientSmoothingRefinementCertificate) : Prop :=
  0 < c.radiusWindow ∧ c.rangeControlled ∧ c.smoothingBudgetControlled

def CoefficientSmoothingRefinementCertificate.size
    (c : CoefficientSmoothingRefinementCertificate) : ℕ :=
  c.radiusWindow + c.rangeWindow + c.smoothingSlackWindow + c.slack

theorem coefficientSmoothing_smoothingBudgetWindow_le_size
    {c : CoefficientSmoothingRefinementCertificate}
    (h : coefficientSmoothingRefinementReady c) :
    c.smoothingBudgetWindow ≤ c.size := by
  rcases h with ⟨_, _, hbudget⟩
  exact hbudget

def sampleCoefficientSmoothingRefinementCertificate :
    CoefficientSmoothingRefinementCertificate :=
  { radiusWindow := 5, rangeWindow := 6, smoothingSlackWindow := 2,
    smoothingBudgetWindow := 14, slack := 1 }

example : coefficientSmoothingRefinementReady
    sampleCoefficientSmoothingRefinementCertificate := by
  norm_num [coefficientSmoothingRefinementReady,
    CoefficientSmoothingRefinementCertificate.rangeControlled,
    CoefficientSmoothingRefinementCertificate.smoothingBudgetControlled,
    sampleCoefficientSmoothingRefinementCertificate]

example :
    sampleCoefficientSmoothingRefinementCertificate.smoothingBudgetWindow ≤
      sampleCoefficientSmoothingRefinementCertificate.size := by
  norm_num [CoefficientSmoothingRefinementCertificate.size,
    sampleCoefficientSmoothingRefinementCertificate]

structure CoefficientSmoothingBudgetCertificate where
  radiusWindow : ℕ
  rangeWindow : ℕ
  smoothingSlackWindow : ℕ
  smoothingBudgetWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def CoefficientSmoothingBudgetCertificate.controlled
    (c : CoefficientSmoothingBudgetCertificate) : Prop :=
  0 < c.radiusWindow ∧
    c.rangeWindow ≤ c.radiusWindow + c.smoothingSlackWindow + c.slack ∧
      c.smoothingBudgetWindow ≤
        c.radiusWindow + c.rangeWindow + c.smoothingSlackWindow + c.slack

def CoefficientSmoothingBudgetCertificate.budgetControlled
    (c : CoefficientSmoothingBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.radiusWindow + c.rangeWindow + c.smoothingSlackWindow +
      c.smoothingBudgetWindow + c.slack

def CoefficientSmoothingBudgetCertificate.Ready
    (c : CoefficientSmoothingBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def CoefficientSmoothingBudgetCertificate.size
    (c : CoefficientSmoothingBudgetCertificate) : ℕ :=
  c.radiusWindow + c.rangeWindow + c.smoothingSlackWindow +
    c.smoothingBudgetWindow + c.slack

theorem coefficientSmoothing_budgetCertificate_le_size
    (c : CoefficientSmoothingBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleCoefficientSmoothingBudgetCertificate :
    CoefficientSmoothingBudgetCertificate :=
  { radiusWindow := 5
    rangeWindow := 6
    smoothingSlackWindow := 2
    smoothingBudgetWindow := 14
    certificateBudgetWindow := 28
    slack := 1 }

example : sampleCoefficientSmoothingBudgetCertificate.Ready := by
  constructor
  · norm_num [CoefficientSmoothingBudgetCertificate.controlled,
      sampleCoefficientSmoothingBudgetCertificate]
  · norm_num [CoefficientSmoothingBudgetCertificate.budgetControlled,
      sampleCoefficientSmoothingBudgetCertificate]

example :
    sampleCoefficientSmoothingBudgetCertificate.certificateBudgetWindow ≤
      sampleCoefficientSmoothingBudgetCertificate.size := by
  apply coefficientSmoothing_budgetCertificate_le_size
  constructor
  · norm_num [CoefficientSmoothingBudgetCertificate.controlled,
      sampleCoefficientSmoothingBudgetCertificate]
  · norm_num [CoefficientSmoothingBudgetCertificate.budgetControlled,
      sampleCoefficientSmoothingBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleCoefficientSmoothingBudgetCertificate.Ready := by
  constructor
  · norm_num [CoefficientSmoothingBudgetCertificate.controlled,
      sampleCoefficientSmoothingBudgetCertificate]
  · norm_num [CoefficientSmoothingBudgetCertificate.budgetControlled,
      sampleCoefficientSmoothingBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleCoefficientSmoothingBudgetCertificate.certificateBudgetWindow ≤
      sampleCoefficientSmoothingBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady
    (data : List CoefficientSmoothingBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleCoefficientSmoothingBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleCoefficientSmoothingBudgetCertificate
  native_decide
end AnalyticCombinatorics.Asymptotics.CoefficientSmoothingWindows
