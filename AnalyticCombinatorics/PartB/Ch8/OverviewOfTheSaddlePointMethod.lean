import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
# Overview of the saddle-point method
-/

namespace AnalyticCombinatorics.PartB.Ch8.OverviewOfTheSaddlePointMethod

/-- Finite saddle-point datum after clearing analytic constants. -/
structure SaddlePointDatum where
  radiusIndex : ℕ
  curvature : ℕ
  errorBudget : ℕ
deriving DecidableEq, Repr

def SaddlePointDatum.valid (d : SaddlePointDatum) : Prop :=
  0 < d.radiusIndex ∧ 0 < d.curvature

theorem saddlePointDatum_sample_valid :
    ({ radiusIndex := 4, curvature := 9,
       errorBudget := 2 } : SaddlePointDatum).valid := by
  norm_num [SaddlePointDatum.valid]

/-- Quadratic saddle envelope in a finite window. -/
def saddleQuadraticEnvelope (curvature distance : ℕ) : ℕ :=
  curvature * distance ^ 2

theorem saddleQuadraticEnvelope_sample :
    saddleQuadraticEnvelope 3 4 = 48 := by
  native_decide

structure SaddleMethodWindow where
  normalizationWindow : ℕ
  contourWindow : ℕ
  errorWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def SaddleMethodWindow.ready (w : SaddleMethodWindow) : Prop :=
  0 < w.normalizationWindow ∧
    w.errorWindow ≤ w.normalizationWindow + w.contourWindow + w.slack

def sampleSaddleMethodWindow : SaddleMethodWindow :=
  { normalizationWindow := 4, contourWindow := 5,
    errorWindow := 10, slack := 1 }

example : sampleSaddleMethodWindow.ready := by
  norm_num [SaddleMethodWindow.ready, sampleSaddleMethodWindow]

structure BudgetCertificate where
  normalizationWindow : ℕ
  contourWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def BudgetCertificate.controlled (c : BudgetCertificate) : Prop :=
  0 < c.normalizationWindow ∧
    c.contourWindow ≤ c.normalizationWindow + c.slack

def BudgetCertificate.budgetControlled (c : BudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.normalizationWindow + c.contourWindow + c.slack

def BudgetCertificate.Ready (c : BudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def BudgetCertificate.size (c : BudgetCertificate) : ℕ :=
  c.normalizationWindow + c.contourWindow + c.slack

def sampleBudgetCertificate : BudgetCertificate :=
  { normalizationWindow := 5, contourWindow := 6,
    certificateBudgetWindow := 12, slack := 1 }

example : sampleBudgetCertificate.Ready := by
  constructor
  · norm_num [BudgetCertificate.controlled, sampleBudgetCertificate]
  · norm_num [BudgetCertificate.budgetControlled, sampleBudgetCertificate]

theorem budgetCertificate_le_size
    (c : BudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  exact h.2

theorem sampleBudgetCertificate_le_size :
    sampleBudgetCertificate.certificateBudgetWindow ≤
      sampleBudgetCertificate.size := by
  have h : sampleBudgetCertificate.Ready := by
    constructor
    · norm_num [BudgetCertificate.controlled,
        sampleBudgetCertificate]
    · norm_num [BudgetCertificate.budgetControlled,
        sampleBudgetCertificate]
  exact h.2

def budgetCertificateListReady (data : List BudgetCertificate) : Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem sampleBudgetCertificate_ready :
    sampleBudgetCertificate.Ready := by
  constructor
  · norm_num [BudgetCertificate.controlled, sampleBudgetCertificate]
  · norm_num [BudgetCertificate.budgetControlled, sampleBudgetCertificate]

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady [sampleBudgetCertificate] = true := by
  unfold budgetCertificateListReady sampleBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch8.OverviewOfTheSaddlePointMethod
