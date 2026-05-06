import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Barrier-function bookkeeping models.

The analytic barrier argument is represented by interior, boundary, and
margin budgets.
-/

namespace AnalyticCombinatorics.AppB.BarrierFunctionModels

structure BarrierDatum where
  interiorValue : ℕ
  boundaryValue : ℕ
  barrierMargin : ℕ
deriving DecidableEq, Repr

def barrierDominates (d : BarrierDatum) : Prop :=
  d.interiorValue + d.barrierMargin ≤ d.boundaryValue

def positiveBarrierMargin (d : BarrierDatum) : Prop :=
  0 < d.barrierMargin

def barrierReady (d : BarrierDatum) : Prop :=
  barrierDominates d ∧ positiveBarrierMargin d

def barrierSlack (d : BarrierDatum) : ℕ :=
  d.boundaryValue - (d.interiorValue + d.barrierMargin)

theorem barrierReady.dominates {d : BarrierDatum}
    (h : barrierReady d) :
    barrierDominates d ∧ positiveBarrierMargin d := by
  refine ⟨h.1, h.2⟩

theorem barrierSlack_add {d : BarrierDatum}
    (h : barrierDominates d) :
    barrierSlack d + (d.interiorValue + d.barrierMargin) = d.boundaryValue := by
  unfold barrierSlack barrierDominates at *
  omega

def sampleBarrier : BarrierDatum :=
  { interiorValue := 3, boundaryValue := 10, barrierMargin := 4 }

example : barrierReady sampleBarrier := by
  norm_num [barrierReady, barrierDominates, positiveBarrierMargin, sampleBarrier]

example : barrierSlack sampleBarrier = 3 := by
  native_decide

structure BarrierWindow where
  interiorValue : ℕ
  boundaryValue : ℕ
  barrierMargin : ℕ
  comparisonSlack : ℕ
deriving DecidableEq, Repr

def BarrierWindow.marginReady (w : BarrierWindow) : Prop :=
  0 < w.barrierMargin

def BarrierWindow.dominates (w : BarrierWindow) : Prop :=
  w.interiorValue + w.barrierMargin ≤ w.boundaryValue + w.comparisonSlack

def BarrierWindow.ready (w : BarrierWindow) : Prop :=
  w.marginReady ∧ w.dominates

def BarrierWindow.certificate (w : BarrierWindow) : ℕ :=
  w.interiorValue + w.boundaryValue + w.barrierMargin + w.comparisonSlack

theorem barrierMargin_le_certificate (w : BarrierWindow) :
    w.barrierMargin ≤ w.certificate := by
  unfold BarrierWindow.certificate
  omega

def sampleBarrierWindow : BarrierWindow :=
  { interiorValue := 3, boundaryValue := 10, barrierMargin := 4, comparisonSlack := 0 }

example : sampleBarrierWindow.ready := by
  norm_num [sampleBarrierWindow, BarrierWindow.ready,
    BarrierWindow.marginReady, BarrierWindow.dominates]


structure BarrierFunctionModelsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def BarrierFunctionModelsBudgetCertificate.controlled
    (c : BarrierFunctionModelsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def BarrierFunctionModelsBudgetCertificate.budgetControlled
    (c : BarrierFunctionModelsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def BarrierFunctionModelsBudgetCertificate.Ready
    (c : BarrierFunctionModelsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def BarrierFunctionModelsBudgetCertificate.size
    (c : BarrierFunctionModelsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem barrierFunctionModels_budgetCertificate_le_size
    (c : BarrierFunctionModelsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleBarrierFunctionModelsBudgetCertificate :
    BarrierFunctionModelsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleBarrierFunctionModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [BarrierFunctionModelsBudgetCertificate.controlled,
      sampleBarrierFunctionModelsBudgetCertificate]
  · norm_num [BarrierFunctionModelsBudgetCertificate.budgetControlled,
      sampleBarrierFunctionModelsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleBarrierFunctionModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleBarrierFunctionModelsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleBarrierFunctionModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [BarrierFunctionModelsBudgetCertificate.controlled,
      sampleBarrierFunctionModelsBudgetCertificate]
  · norm_num [BarrierFunctionModelsBudgetCertificate.budgetControlled,
      sampleBarrierFunctionModelsBudgetCertificate]

example :
    sampleBarrierFunctionModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleBarrierFunctionModelsBudgetCertificate.size := by
  apply barrierFunctionModels_budgetCertificate_le_size
  constructor
  · norm_num [BarrierFunctionModelsBudgetCertificate.controlled,
      sampleBarrierFunctionModelsBudgetCertificate]
  · norm_num [BarrierFunctionModelsBudgetCertificate.budgetControlled,
      sampleBarrierFunctionModelsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List BarrierFunctionModelsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleBarrierFunctionModelsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleBarrierFunctionModelsBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppB.BarrierFunctionModels
