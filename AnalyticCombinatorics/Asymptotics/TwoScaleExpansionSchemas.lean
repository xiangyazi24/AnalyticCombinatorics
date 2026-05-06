import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Two-scale expansion bookkeeping.

This file models the integer scale separation and remainder budget used by
matched asymptotic expansions.
-/

namespace AnalyticCombinatorics.Asymptotics.TwoScaleExpansionSchemas

structure TwoScaleData where
  slowScale : ℕ
  fastScale : ℕ
  remainder : ℕ
deriving DecidableEq, Repr

def scaleSeparated (d : TwoScaleData) : Prop :=
  d.slowScale < d.fastScale

def twoScaleReady (d : TwoScaleData) : Prop :=
  0 < d.slowScale ∧ scaleSeparated d ∧ d.remainder ≤ d.fastScale

def scaleGap (d : TwoScaleData) : ℕ :=
  d.fastScale - d.slowScale

theorem twoScaleReady.separated {d : TwoScaleData}
    (h : twoScaleReady d) :
    scaleSeparated d := h.2.1

theorem scaleGap_positive {d : TwoScaleData}
    (h : scaleSeparated d) :
    0 < scaleGap d := by
  unfold scaleSeparated scaleGap at *
  omega

def sampleTwoScale : TwoScaleData :=
  { slowScale := 3, fastScale := 10, remainder := 4 }

example : twoScaleReady sampleTwoScale := by
  norm_num [twoScaleReady, scaleSeparated, sampleTwoScale]

example : scaleGap sampleTwoScale = 7 := by
  native_decide

/-- Finite executable readiness audit for two-scale expansion data. -/
def twoScaleDataListReady (data : List TwoScaleData) : Bool :=
  data.all fun d => 0 < d.slowScale && d.slowScale < d.fastScale && d.remainder ≤ d.fastScale

theorem twoScaleDataList_readyWindow :
    twoScaleDataListReady
      [{ slowScale := 2, fastScale := 6, remainder := 3 },
       { slowScale := 3, fastScale := 10, remainder := 4 }] = true := by
  unfold twoScaleDataListReady
  native_decide

structure TwoScaleWindow where
  slowScale : ℕ
  fastScale : ℕ
  matchingIndex : ℕ
  remainderBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def TwoScaleWindow.separated (w : TwoScaleWindow) : Prop :=
  w.slowScale < w.fastScale

def TwoScaleWindow.matchingControlled (w : TwoScaleWindow) : Prop :=
  w.matchingIndex ≤ w.fastScale + w.slack

def TwoScaleWindow.ready (w : TwoScaleWindow) : Prop :=
  0 < w.slowScale ∧ w.separated ∧ w.matchingControlled ∧
    w.remainderBudget ≤ w.fastScale + w.slack

def TwoScaleWindow.certificate (w : TwoScaleWindow) : ℕ :=
  w.slowScale + w.fastScale + w.matchingIndex + w.remainderBudget + w.slack

theorem remainderBudget_le_certificate (w : TwoScaleWindow) :
    w.remainderBudget ≤ w.certificate := by
  unfold TwoScaleWindow.certificate
  omega

def sampleTwoScaleWindow : TwoScaleWindow :=
  { slowScale := 3, fastScale := 10, matchingIndex := 8, remainderBudget := 4, slack := 0 }

example : sampleTwoScaleWindow.ready := by
  norm_num [sampleTwoScaleWindow, TwoScaleWindow.ready, TwoScaleWindow.separated,
    TwoScaleWindow.matchingControlled]

/-- A refinement certificate for two-scale expansion windows. -/
structure TwoScaleExpansionCertificate where
  slowWindow : ℕ
  fastWindow : ℕ
  matchingWindow : ℕ
  remainderWindow : ℕ
  slack : ℕ

/-- The fast scale dominates the slow scale and controls matching data. -/
def twoScaleExpansionCertificateControlled
    (w : TwoScaleExpansionCertificate) : Prop :=
  0 < w.slowWindow ∧
    w.slowWindow < w.fastWindow ∧
      w.matchingWindow ≤ w.fastWindow + w.slack ∧
        w.remainderWindow ≤ w.fastWindow + w.slack

/-- Readiness for a two-scale expansion certificate. -/
def twoScaleExpansionCertificateReady
    (w : TwoScaleExpansionCertificate) : Prop :=
  twoScaleExpansionCertificateControlled w ∧
    w.remainderWindow ≤
      w.slowWindow + w.fastWindow + w.matchingWindow + w.remainderWindow + w.slack

/-- Total size of a two-scale expansion certificate. -/
def twoScaleExpansionCertificateSize
    (w : TwoScaleExpansionCertificate) : ℕ :=
  w.slowWindow + w.fastWindow + w.matchingWindow + w.remainderWindow + w.slack

theorem twoScaleExpansionCertificate_remainder_le_size
    (w : TwoScaleExpansionCertificate)
    (h : twoScaleExpansionCertificateReady w) :
    w.remainderWindow ≤ twoScaleExpansionCertificateSize w := by
  rcases h with ⟨_, hbudget⟩
  unfold twoScaleExpansionCertificateSize
  omega

def sampleTwoScaleExpansionCertificate :
    TwoScaleExpansionCertificate where
  slowWindow := 3
  fastWindow := 10
  matchingWindow := 8
  remainderWindow := 4
  slack := 0

example :
    twoScaleExpansionCertificateReady sampleTwoScaleExpansionCertificate := by
  norm_num [twoScaleExpansionCertificateReady,
    twoScaleExpansionCertificateControlled, sampleTwoScaleExpansionCertificate]

example :
    sampleTwoScaleExpansionCertificate.remainderWindow ≤
      twoScaleExpansionCertificateSize sampleTwoScaleExpansionCertificate := by
  apply twoScaleExpansionCertificate_remainder_le_size
  norm_num [twoScaleExpansionCertificateReady,
    twoScaleExpansionCertificateControlled, sampleTwoScaleExpansionCertificate]

/-- A refinement certificate with the two-scale budget separated from size. -/
structure TwoScaleExpansionRefinementCertificate where
  slowWindow : ℕ
  fastWindow : ℕ
  matchingWindow : ℕ
  remainderWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ

def TwoScaleExpansionRefinementCertificate.scaleControlled
    (cert : TwoScaleExpansionRefinementCertificate) : Prop :=
  0 < cert.slowWindow ∧
    cert.slowWindow < cert.fastWindow ∧
      cert.matchingWindow ≤ cert.fastWindow + cert.slack ∧
        cert.remainderWindow ≤ cert.fastWindow + cert.slack

def TwoScaleExpansionRefinementCertificate.budgetControlled
    (cert : TwoScaleExpansionRefinementCertificate) : Prop :=
  cert.certificateBudgetWindow ≤
    cert.slowWindow + cert.fastWindow + cert.matchingWindow +
      cert.remainderWindow + cert.slack

def twoScaleExpansionRefinementReady
    (cert : TwoScaleExpansionRefinementCertificate) : Prop :=
  cert.scaleControlled ∧ cert.budgetControlled

def TwoScaleExpansionRefinementCertificate.size
    (cert : TwoScaleExpansionRefinementCertificate) : ℕ :=
  cert.slowWindow + cert.fastWindow + cert.matchingWindow +
    cert.remainderWindow + cert.slack

theorem twoScaleExpansion_certificateBudgetWindow_le_size
    (cert : TwoScaleExpansionRefinementCertificate)
    (h : twoScaleExpansionRefinementReady cert) :
    cert.certificateBudgetWindow ≤ cert.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleTwoScaleExpansionRefinementCertificate :
    TwoScaleExpansionRefinementCertificate where
  slowWindow := 3
  fastWindow := 10
  matchingWindow := 8
  remainderWindow := 4
  certificateBudgetWindow := 25
  slack := 0

example :
    twoScaleExpansionRefinementReady sampleTwoScaleExpansionRefinementCertificate := by
  norm_num [twoScaleExpansionRefinementReady,
    TwoScaleExpansionRefinementCertificate.scaleControlled,
    TwoScaleExpansionRefinementCertificate.budgetControlled,
    sampleTwoScaleExpansionRefinementCertificate]

example :
    sampleTwoScaleExpansionRefinementCertificate.certificateBudgetWindow ≤
      sampleTwoScaleExpansionRefinementCertificate.size := by
  apply twoScaleExpansion_certificateBudgetWindow_le_size
  norm_num [twoScaleExpansionRefinementReady,
    TwoScaleExpansionRefinementCertificate.scaleControlled,
    TwoScaleExpansionRefinementCertificate.budgetControlled,
    sampleTwoScaleExpansionRefinementCertificate]


structure TwoScaleExpansionSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def TwoScaleExpansionSchemasBudgetCertificate.controlled
    (c : TwoScaleExpansionSchemasBudgetCertificate) : Prop :=
  0 < c.primaryWindow ∧ c.secondaryWindow ≤ c.primaryWindow + c.slack

def TwoScaleExpansionSchemasBudgetCertificate.budgetControlled
    (c : TwoScaleExpansionSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def TwoScaleExpansionSchemasBudgetCertificate.Ready
    (c : TwoScaleExpansionSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def TwoScaleExpansionSchemasBudgetCertificate.size
    (c : TwoScaleExpansionSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem twoScaleExpansionSchemas_budgetCertificate_le_size
    (c : TwoScaleExpansionSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleTwoScaleExpansionSchemasBudgetCertificate :
    TwoScaleExpansionSchemasBudgetCertificate :=
  { primaryWindow := 5
    secondaryWindow := 6
    certificateBudgetWindow := 12
    slack := 1 }

example : sampleTwoScaleExpansionSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [TwoScaleExpansionSchemasBudgetCertificate.controlled,
      sampleTwoScaleExpansionSchemasBudgetCertificate]
  · norm_num [TwoScaleExpansionSchemasBudgetCertificate.budgetControlled,
      sampleTwoScaleExpansionSchemasBudgetCertificate]

example :
    sampleTwoScaleExpansionSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleTwoScaleExpansionSchemasBudgetCertificate.size := by
  apply twoScaleExpansionSchemas_budgetCertificate_le_size
  constructor
  · norm_num [TwoScaleExpansionSchemasBudgetCertificate.controlled,
      sampleTwoScaleExpansionSchemasBudgetCertificate]
  · norm_num [TwoScaleExpansionSchemasBudgetCertificate.budgetControlled,
      sampleTwoScaleExpansionSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleTwoScaleExpansionSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [TwoScaleExpansionSchemasBudgetCertificate.controlled,
      sampleTwoScaleExpansionSchemasBudgetCertificate]
  · norm_num [TwoScaleExpansionSchemasBudgetCertificate.budgetControlled,
      sampleTwoScaleExpansionSchemasBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleTwoScaleExpansionSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleTwoScaleExpansionSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady
    (data : List TwoScaleExpansionSchemasBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleTwoScaleExpansionSchemasBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleTwoScaleExpansionSchemasBudgetCertificate
  native_decide
end AnalyticCombinatorics.Asymptotics.TwoScaleExpansionSchemas
