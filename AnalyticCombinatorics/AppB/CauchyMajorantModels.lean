import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Cauchy majorant models.

The finite abstraction stores radius margin, coefficient majorant, and
contour slack.
-/

namespace AnalyticCombinatorics.AppB.CauchyMajorantModels

structure CauchyMajorantData where
  radiusMargin : ℕ
  coefficientMajorant : ℕ
  contourSlack : ℕ
deriving DecidableEq, Repr

def radiusMarginPositive (d : CauchyMajorantData) : Prop :=
  0 < d.radiusMargin

def majorantControlled (d : CauchyMajorantData) : Prop :=
  d.coefficientMajorant ≤ d.radiusMargin + d.contourSlack

def cauchyMajorantReady (d : CauchyMajorantData) : Prop :=
  radiusMarginPositive d ∧ majorantControlled d

def cauchyMajorantBudget (d : CauchyMajorantData) : ℕ :=
  d.radiusMargin + d.coefficientMajorant + d.contourSlack

theorem cauchyMajorantReady.radius {d : CauchyMajorantData}
    (h : cauchyMajorantReady d) :
    radiusMarginPositive d ∧ majorantControlled d ∧
      d.coefficientMajorant ≤ cauchyMajorantBudget d := by
  refine ⟨h.1, h.2, ?_⟩
  unfold cauchyMajorantBudget
  omega

theorem coefficientMajorant_le_cauchyBudget (d : CauchyMajorantData) :
    d.coefficientMajorant ≤ cauchyMajorantBudget d := by
  unfold cauchyMajorantBudget
  omega

def sampleCauchyMajorantData : CauchyMajorantData :=
  { radiusMargin := 6, coefficientMajorant := 8, contourSlack := 3 }

example : cauchyMajorantReady sampleCauchyMajorantData := by
  norm_num [cauchyMajorantReady, radiusMarginPositive]
  norm_num [majorantControlled, sampleCauchyMajorantData]

example : cauchyMajorantBudget sampleCauchyMajorantData = 17 := by
  native_decide

/-- Finite executable readiness audit for Cauchy majorant windows. -/
def cauchyMajorantListReady (windows : List CauchyMajorantData) : Bool :=
  windows.all fun d =>
    0 < d.radiusMargin &&
      d.coefficientMajorant ≤ d.radiusMargin + d.contourSlack

theorem cauchyMajorantList_readyWindow :
    cauchyMajorantListReady
      [{ radiusMargin := 4, coefficientMajorant := 5, contourSlack := 1 },
       { radiusMargin := 6, coefficientMajorant := 8, contourSlack := 3 }] = true := by
  unfold cauchyMajorantListReady
  native_decide


structure CauchyMajorantModelsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def CauchyMajorantModelsBudgetCertificate.controlled
    (c : CauchyMajorantModelsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def CauchyMajorantModelsBudgetCertificate.budgetControlled
    (c : CauchyMajorantModelsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def CauchyMajorantModelsBudgetCertificate.Ready
    (c : CauchyMajorantModelsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def CauchyMajorantModelsBudgetCertificate.size
    (c : CauchyMajorantModelsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem cauchyMajorantModels_budgetCertificate_le_size
    (c : CauchyMajorantModelsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleCauchyMajorantModelsBudgetCertificate :
    CauchyMajorantModelsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleCauchyMajorantModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [CauchyMajorantModelsBudgetCertificate.controlled,
      sampleCauchyMajorantModelsBudgetCertificate]
  · norm_num [CauchyMajorantModelsBudgetCertificate.budgetControlled,
      sampleCauchyMajorantModelsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleCauchyMajorantModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleCauchyMajorantModelsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleCauchyMajorantModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [CauchyMajorantModelsBudgetCertificate.controlled,
      sampleCauchyMajorantModelsBudgetCertificate]
  · norm_num [CauchyMajorantModelsBudgetCertificate.budgetControlled,
      sampleCauchyMajorantModelsBudgetCertificate]

example :
    sampleCauchyMajorantModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleCauchyMajorantModelsBudgetCertificate.size := by
  apply cauchyMajorantModels_budgetCertificate_le_size
  constructor
  · norm_num [CauchyMajorantModelsBudgetCertificate.controlled,
      sampleCauchyMajorantModelsBudgetCertificate]
  · norm_num [CauchyMajorantModelsBudgetCertificate.budgetControlled,
      sampleCauchyMajorantModelsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady
    (data : List CauchyMajorantModelsBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleCauchyMajorantModelsBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleCauchyMajorantModelsBudgetCertificate
  native_decide
end AnalyticCombinatorics.AppB.CauchyMajorantModels
