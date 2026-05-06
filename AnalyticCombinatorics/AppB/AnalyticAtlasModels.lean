import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Analytic atlas bookkeeping.

The finite schema records chart counts, transition counts, and compatibility
budgets.
-/

namespace AnalyticCombinatorics.AppB.AnalyticAtlasModels

structure AtlasDatum where
  chartCount : ℕ
  transitionCount : ℕ
  compatibilityBudget : ℕ
deriving DecidableEq, Repr

def nonemptyAtlas (d : AtlasDatum) : Prop :=
  0 < d.chartCount

def transitionsControlled (d : AtlasDatum) : Prop :=
  d.transitionCount ≤ d.chartCount * d.chartCount

def atlasReady (d : AtlasDatum) : Prop :=
  nonemptyAtlas d ∧ transitionsControlled d

def atlasComplexity (d : AtlasDatum) : ℕ :=
  d.chartCount + d.transitionCount + d.compatibilityBudget

theorem atlasReady.nonempty {d : AtlasDatum}
    (h : atlasReady d) :
    nonemptyAtlas d ∧ transitionsControlled d ∧ d.transitionCount ≤ atlasComplexity d := by
  refine ⟨h.1, h.2, ?_⟩
  unfold atlasComplexity
  omega

theorem chartCount_le_atlasComplexity (d : AtlasDatum) :
    d.chartCount ≤ atlasComplexity d := by
  unfold atlasComplexity
  omega

def sampleAtlas : AtlasDatum :=
  { chartCount := 4, transitionCount := 10, compatibilityBudget := 3 }

example : atlasReady sampleAtlas := by
  norm_num [atlasReady, nonemptyAtlas, transitionsControlled, sampleAtlas]

example : atlasComplexity sampleAtlas = 17 := by
  native_decide

structure AtlasWindow where
  chartCount : ℕ
  transitionCount : ℕ
  compatibilityBudget : ℕ
  overlapBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def AtlasWindow.transitionsControlled (w : AtlasWindow) : Prop :=
  w.transitionCount ≤ w.chartCount * w.chartCount + w.slack

def AtlasWindow.overlapControlled (w : AtlasWindow) : Prop :=
  w.overlapBudget ≤ w.chartCount + w.transitionCount + w.compatibilityBudget + w.slack

def atlasWindowReady (w : AtlasWindow) : Prop :=
  0 < w.chartCount ∧
    w.transitionsControlled ∧
    w.overlapControlled

def AtlasWindow.certificate (w : AtlasWindow) : ℕ :=
  w.chartCount + w.transitionCount + w.compatibilityBudget + w.slack

theorem atlas_overlapBudget_le_certificate {w : AtlasWindow}
    (h : atlasWindowReady w) :
    w.overlapBudget ≤ w.certificate := by
  rcases h with ⟨_, _, hoverlap⟩
  exact hoverlap

def sampleAtlasWindow : AtlasWindow :=
  { chartCount := 4, transitionCount := 10, compatibilityBudget := 3, overlapBudget := 16,
    slack := 0 }

example : atlasWindowReady sampleAtlasWindow := by
  norm_num [atlasWindowReady, AtlasWindow.transitionsControlled, AtlasWindow.overlapControlled,
    sampleAtlasWindow]

example : sampleAtlasWindow.certificate = 17 := by
  native_decide


structure AnalyticAtlasModelsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def AnalyticAtlasModelsBudgetCertificate.controlled
    (c : AnalyticAtlasModelsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def AnalyticAtlasModelsBudgetCertificate.budgetControlled
    (c : AnalyticAtlasModelsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def AnalyticAtlasModelsBudgetCertificate.Ready
    (c : AnalyticAtlasModelsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def AnalyticAtlasModelsBudgetCertificate.size
    (c : AnalyticAtlasModelsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem analyticAtlasModels_budgetCertificate_le_size
    (c : AnalyticAtlasModelsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleAnalyticAtlasModelsBudgetCertificate :
    AnalyticAtlasModelsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleAnalyticAtlasModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [AnalyticAtlasModelsBudgetCertificate.controlled,
      sampleAnalyticAtlasModelsBudgetCertificate]
  · norm_num [AnalyticAtlasModelsBudgetCertificate.budgetControlled,
      sampleAnalyticAtlasModelsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleAnalyticAtlasModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleAnalyticAtlasModelsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleAnalyticAtlasModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [AnalyticAtlasModelsBudgetCertificate.controlled,
      sampleAnalyticAtlasModelsBudgetCertificate]
  · norm_num [AnalyticAtlasModelsBudgetCertificate.budgetControlled,
      sampleAnalyticAtlasModelsBudgetCertificate]

example :
    sampleAnalyticAtlasModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleAnalyticAtlasModelsBudgetCertificate.size := by
  apply analyticAtlasModels_budgetCertificate_le_size
  constructor
  · norm_num [AnalyticAtlasModelsBudgetCertificate.controlled,
      sampleAnalyticAtlasModelsBudgetCertificate]
  · norm_num [AnalyticAtlasModelsBudgetCertificate.budgetControlled,
      sampleAnalyticAtlasModelsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List AnalyticAtlasModelsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleAnalyticAtlasModelsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleAnalyticAtlasModelsBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppB.AnalyticAtlasModels
