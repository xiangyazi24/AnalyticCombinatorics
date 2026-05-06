import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Slow-variation schema bookkeeping.

The finite data tracks a scale window and a ratio budget for regular
variation arguments.
-/

namespace AnalyticCombinatorics.AppC.SlowVariationSchemas

structure SlowVariationData where
  scaleStart : ℕ
  scaleEnd : ℕ
  ratioBudget : ℕ
deriving DecidableEq, Repr

def nonemptyScaleWindow (d : SlowVariationData) : Prop :=
  d.scaleStart ≤ d.scaleEnd

def ratioControlled (d : SlowVariationData) : Prop :=
  0 < d.ratioBudget

def slowVariationReady (d : SlowVariationData) : Prop :=
  nonemptyScaleWindow d ∧ ratioControlled d

def scaleWindowLength (d : SlowVariationData) : ℕ :=
  d.scaleEnd - d.scaleStart + 1

theorem slowVariationReady.window {d : SlowVariationData}
    (h : slowVariationReady d) :
    nonemptyScaleWindow d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem scaleWindowLength_positive (d : SlowVariationData) :
    0 < scaleWindowLength d := by
  unfold scaleWindowLength
  omega

def sampleSlowVariation : SlowVariationData :=
  { scaleStart := 4, scaleEnd := 9, ratioBudget := 2 }

example : slowVariationReady sampleSlowVariation := by
  norm_num [slowVariationReady, nonemptyScaleWindow, ratioControlled, sampleSlowVariation]

example : scaleWindowLength sampleSlowVariation = 6 := by
  native_decide

structure SlowVariationWindow where
  scaleStart : ℕ
  scaleEnd : ℕ
  ratioBudget : ℕ
  comparisonMass : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def SlowVariationWindow.windowReady (w : SlowVariationWindow) : Prop :=
  w.scaleStart ≤ w.scaleEnd ∧ 0 < w.ratioBudget

def SlowVariationWindow.comparisonControlled (w : SlowVariationWindow) : Prop :=
  w.comparisonMass ≤ (w.scaleEnd - w.scaleStart + 1) * w.ratioBudget + w.slack

def SlowVariationWindow.ready (w : SlowVariationWindow) : Prop :=
  w.windowReady ∧ w.comparisonControlled

def SlowVariationWindow.certificate (w : SlowVariationWindow) : ℕ :=
  w.scaleStart + w.scaleEnd + w.ratioBudget + w.comparisonMass + w.slack

theorem ratioBudget_le_certificate (w : SlowVariationWindow) :
    w.ratioBudget ≤ w.certificate := by
  unfold SlowVariationWindow.certificate
  omega

def sampleSlowVariationWindow : SlowVariationWindow :=
  { scaleStart := 4, scaleEnd := 9, ratioBudget := 2, comparisonMass := 10, slack := 0 }

example : sampleSlowVariationWindow.ready := by
  norm_num [sampleSlowVariationWindow, SlowVariationWindow.ready,
    SlowVariationWindow.windowReady, SlowVariationWindow.comparisonControlled]

structure SlowVariationRefinementWindow where
  startWindow : ℕ
  endWindow : ℕ
  ratioWindow : ℕ
  comparisonWindow : ℕ
  slowBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def SlowVariationRefinementWindow.windowReady
    (w : SlowVariationRefinementWindow) : Prop :=
  w.startWindow ≤ w.endWindow ∧ 0 < w.ratioWindow

def SlowVariationRefinementWindow.comparisonControlled
    (w : SlowVariationRefinementWindow) : Prop :=
  w.comparisonWindow ≤ (w.endWindow - w.startWindow + 1) * w.ratioWindow + w.slack

def slowVariationRefinementWindowReady
    (w : SlowVariationRefinementWindow) : Prop :=
  w.windowReady ∧ w.comparisonControlled ∧
    w.slowBudget ≤ w.startWindow + w.endWindow + w.comparisonWindow + w.slack

def SlowVariationRefinementWindow.certificate
    (w : SlowVariationRefinementWindow) : ℕ :=
  w.startWindow + w.endWindow + w.ratioWindow + w.comparisonWindow + w.slowBudget + w.slack

theorem slowVariationRefinement_budget_le_certificate
    (w : SlowVariationRefinementWindow) :
    w.slowBudget ≤ w.certificate := by
  unfold SlowVariationRefinementWindow.certificate
  omega

def sampleSlowVariationRefinementWindow : SlowVariationRefinementWindow :=
  { startWindow := 4, endWindow := 9, ratioWindow := 2,
    comparisonWindow := 10, slowBudget := 24, slack := 1 }

example : slowVariationRefinementWindowReady
    sampleSlowVariationRefinementWindow := by
  norm_num [slowVariationRefinementWindowReady,
    SlowVariationRefinementWindow.windowReady,
    SlowVariationRefinementWindow.comparisonControlled,
    sampleSlowVariationRefinementWindow]


structure SlowVariationSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def SlowVariationSchemasBudgetCertificate.controlled
    (c : SlowVariationSchemasBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def SlowVariationSchemasBudgetCertificate.budgetControlled
    (c : SlowVariationSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def SlowVariationSchemasBudgetCertificate.Ready
    (c : SlowVariationSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def SlowVariationSchemasBudgetCertificate.size
    (c : SlowVariationSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem slowVariationSchemas_budgetCertificate_le_size
    (c : SlowVariationSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleSlowVariationSchemasBudgetCertificate :
    SlowVariationSchemasBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

example : sampleSlowVariationSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [SlowVariationSchemasBudgetCertificate.controlled,
      sampleSlowVariationSchemasBudgetCertificate]
  · norm_num [SlowVariationSchemasBudgetCertificate.budgetControlled,
      sampleSlowVariationSchemasBudgetCertificate]

example :
    sampleSlowVariationSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleSlowVariationSchemasBudgetCertificate.size := by
  apply slowVariationSchemas_budgetCertificate_le_size
  constructor
  · norm_num [SlowVariationSchemasBudgetCertificate.controlled,
      sampleSlowVariationSchemasBudgetCertificate]
  · norm_num [SlowVariationSchemasBudgetCertificate.budgetControlled,
      sampleSlowVariationSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleSlowVariationSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [SlowVariationSchemasBudgetCertificate.controlled,
      sampleSlowVariationSchemasBudgetCertificate]
  · norm_num [SlowVariationSchemasBudgetCertificate.budgetControlled,
      sampleSlowVariationSchemasBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleSlowVariationSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleSlowVariationSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List SlowVariationSchemasBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleSlowVariationSchemasBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleSlowVariationSchemasBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppC.SlowVariationSchemas
