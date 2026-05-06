import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Finite cycle index window models.

This module records finite bookkeeping for cycle index windows.
-/

namespace AnalyticCombinatorics.AppA.FiniteCycleIndexWindowModels

structure CycleIndexWindowData where
  cycleTypes : ℕ
  indexWindow : ℕ
  cycleSlack : ℕ
deriving DecidableEq, Repr

def hasCycleTypes (d : CycleIndexWindowData) : Prop :=
  0 < d.cycleTypes

def indexWindowControlled (d : CycleIndexWindowData) : Prop :=
  d.indexWindow ≤ d.cycleTypes + d.cycleSlack

def cycleIndexWindowReady (d : CycleIndexWindowData) : Prop :=
  hasCycleTypes d ∧ indexWindowControlled d

def cycleIndexWindowBudget (d : CycleIndexWindowData) : ℕ :=
  d.cycleTypes + d.indexWindow + d.cycleSlack

theorem cycleIndexWindowReady.hasCycleTypes
    {d : CycleIndexWindowData}
    (h : cycleIndexWindowReady d) :
    hasCycleTypes d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem indexWindow_le_budget (d : CycleIndexWindowData) :
    d.indexWindow ≤ cycleIndexWindowBudget d := by
  unfold cycleIndexWindowBudget
  omega

def sampleCycleIndexWindowData : CycleIndexWindowData :=
  { cycleTypes := 6, indexWindow := 8, cycleSlack := 3 }

example : cycleIndexWindowReady sampleCycleIndexWindowData := by
  norm_num [cycleIndexWindowReady, hasCycleTypes]
  norm_num [indexWindowControlled, sampleCycleIndexWindowData]

example : cycleIndexWindowBudget sampleCycleIndexWindowData = 17 := by
  native_decide

structure CycleIndexCertificateWindow where
  cycleTypes : ℕ
  indexWindow : ℕ
  cycleSlack : ℕ
  monomialBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def CycleIndexCertificateWindow.indexControlled (w : CycleIndexCertificateWindow) : Prop :=
  w.indexWindow ≤ w.cycleTypes + w.cycleSlack + w.slack

def CycleIndexCertificateWindow.monomialControlled (w : CycleIndexCertificateWindow) : Prop :=
  w.monomialBudget ≤ w.cycleTypes + w.indexWindow + w.cycleSlack + w.slack

def cycleIndexCertificateReady (w : CycleIndexCertificateWindow) : Prop :=
  0 < w.cycleTypes ∧
    w.indexControlled ∧
    w.monomialControlled

def CycleIndexCertificateWindow.certificate (w : CycleIndexCertificateWindow) : ℕ :=
  w.cycleTypes + w.indexWindow + w.cycleSlack + w.slack

theorem cycleIndex_monomial_le_certificate {w : CycleIndexCertificateWindow}
    (h : cycleIndexCertificateReady w) :
    w.monomialBudget ≤ w.certificate := by
  rcases h with ⟨_, _, hmono⟩
  exact hmono

def sampleCycleIndexCertificateWindow : CycleIndexCertificateWindow :=
  { cycleTypes := 6, indexWindow := 8, cycleSlack := 3, monomialBudget := 16, slack := 0 }

example : cycleIndexCertificateReady sampleCycleIndexCertificateWindow := by
  norm_num [cycleIndexCertificateReady, CycleIndexCertificateWindow.indexControlled,
    CycleIndexCertificateWindow.monomialControlled, sampleCycleIndexCertificateWindow]

example : sampleCycleIndexCertificateWindow.certificate = 17 := by
  native_decide


structure FiniteCycleIndexWindowModelsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def FiniteCycleIndexWindowModelsBudgetCertificate.controlled
    (c : FiniteCycleIndexWindowModelsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def FiniteCycleIndexWindowModelsBudgetCertificate.budgetControlled
    (c : FiniteCycleIndexWindowModelsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def FiniteCycleIndexWindowModelsBudgetCertificate.Ready
    (c : FiniteCycleIndexWindowModelsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def FiniteCycleIndexWindowModelsBudgetCertificate.size
    (c : FiniteCycleIndexWindowModelsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem finiteCycleIndexWindowModels_budgetCertificate_le_size
    (c : FiniteCycleIndexWindowModelsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleFiniteCycleIndexWindowModelsBudgetCertificate :
    FiniteCycleIndexWindowModelsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleFiniteCycleIndexWindowModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [FiniteCycleIndexWindowModelsBudgetCertificate.controlled,
      sampleFiniteCycleIndexWindowModelsBudgetCertificate]
  · norm_num [FiniteCycleIndexWindowModelsBudgetCertificate.budgetControlled,
      sampleFiniteCycleIndexWindowModelsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleFiniteCycleIndexWindowModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleFiniteCycleIndexWindowModelsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleFiniteCycleIndexWindowModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [FiniteCycleIndexWindowModelsBudgetCertificate.controlled,
      sampleFiniteCycleIndexWindowModelsBudgetCertificate]
  · norm_num [FiniteCycleIndexWindowModelsBudgetCertificate.budgetControlled,
      sampleFiniteCycleIndexWindowModelsBudgetCertificate]

example :
    sampleFiniteCycleIndexWindowModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleFiniteCycleIndexWindowModelsBudgetCertificate.size := by
  apply finiteCycleIndexWindowModels_budgetCertificate_le_size
  constructor
  · norm_num [FiniteCycleIndexWindowModelsBudgetCertificate.controlled,
      sampleFiniteCycleIndexWindowModelsBudgetCertificate]
  · norm_num [FiniteCycleIndexWindowModelsBudgetCertificate.budgetControlled,
      sampleFiniteCycleIndexWindowModelsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List FiniteCycleIndexWindowModelsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleFiniteCycleIndexWindowModelsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleFiniteCycleIndexWindowModelsBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppA.FiniteCycleIndexWindowModels
