import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Finite cycle substitution models.

This module records finite bookkeeping for substituting structures into cycles.
-/

namespace AnalyticCombinatorics.AppA.FiniteCycleSubstitutionModels

structure CycleSubstitutionData where
  cycleSlots : ℕ
  substitutionCount : ℕ
  substitutionSlack : ℕ
deriving DecidableEq, Repr

def hasCycleSlots (d : CycleSubstitutionData) : Prop :=
  0 < d.cycleSlots

def substitutionCountControlled (d : CycleSubstitutionData) : Prop :=
  d.substitutionCount ≤ d.cycleSlots + d.substitutionSlack

def cycleSubstitutionReady (d : CycleSubstitutionData) : Prop :=
  hasCycleSlots d ∧ substitutionCountControlled d

def cycleSubstitutionBudget (d : CycleSubstitutionData) : ℕ :=
  d.cycleSlots + d.substitutionCount + d.substitutionSlack

theorem cycleSubstitutionReady.hasCycleSlots {d : CycleSubstitutionData}
    (h : cycleSubstitutionReady d) :
    hasCycleSlots d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem substitutionCount_le_budget (d : CycleSubstitutionData) :
    d.substitutionCount ≤ cycleSubstitutionBudget d := by
  unfold cycleSubstitutionBudget
  omega

def sampleCycleSubstitutionData : CycleSubstitutionData :=
  { cycleSlots := 7, substitutionCount := 9, substitutionSlack := 3 }

example : cycleSubstitutionReady sampleCycleSubstitutionData := by
  norm_num [cycleSubstitutionReady, hasCycleSlots]
  norm_num [substitutionCountControlled, sampleCycleSubstitutionData]

example : cycleSubstitutionBudget sampleCycleSubstitutionData = 19 := by
  native_decide

structure CycleSubstitutionWindow where
  cycleSlots : ℕ
  substitutionCount : ℕ
  substitutionSlack : ℕ
  substitutedCycleBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def CycleSubstitutionWindow.substitutionControlled (w : CycleSubstitutionWindow) : Prop :=
  w.substitutionCount ≤ w.cycleSlots + w.substitutionSlack + w.slack

def CycleSubstitutionWindow.substitutedCycleControlled (w : CycleSubstitutionWindow) : Prop :=
  w.substitutedCycleBudget ≤ w.cycleSlots + w.substitutionCount + w.substitutionSlack + w.slack

def cycleSubstitutionWindowReady (w : CycleSubstitutionWindow) : Prop :=
  0 < w.cycleSlots ∧
    w.substitutionControlled ∧
    w.substitutedCycleControlled

def CycleSubstitutionWindow.certificate (w : CycleSubstitutionWindow) : ℕ :=
  w.cycleSlots + w.substitutionCount + w.substitutionSlack + w.slack

theorem cycleSubstitution_substitutedCycleBudget_le_certificate {w : CycleSubstitutionWindow}
    (h : cycleSubstitutionWindowReady w) :
    w.substitutedCycleBudget ≤ w.certificate := by
  rcases h with ⟨_, _, hsubst⟩
  exact hsubst

def sampleCycleSubstitutionWindow : CycleSubstitutionWindow :=
  { cycleSlots := 7, substitutionCount := 9, substitutionSlack := 3, substitutedCycleBudget := 18,
    slack := 0 }

example : cycleSubstitutionWindowReady sampleCycleSubstitutionWindow := by
  norm_num [cycleSubstitutionWindowReady, CycleSubstitutionWindow.substitutionControlled,
    CycleSubstitutionWindow.substitutedCycleControlled, sampleCycleSubstitutionWindow]

example : sampleCycleSubstitutionWindow.certificate = 19 := by
  native_decide


structure FiniteCycleSubstitutionModelsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def FiniteCycleSubstitutionModelsBudgetCertificate.controlled
    (c : FiniteCycleSubstitutionModelsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def FiniteCycleSubstitutionModelsBudgetCertificate.budgetControlled
    (c : FiniteCycleSubstitutionModelsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def FiniteCycleSubstitutionModelsBudgetCertificate.Ready
    (c : FiniteCycleSubstitutionModelsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def FiniteCycleSubstitutionModelsBudgetCertificate.size
    (c : FiniteCycleSubstitutionModelsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem finiteCycleSubstitutionModels_budgetCertificate_le_size
    (c : FiniteCycleSubstitutionModelsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleFiniteCycleSubstitutionModelsBudgetCertificate :
    FiniteCycleSubstitutionModelsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleFiniteCycleSubstitutionModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [FiniteCycleSubstitutionModelsBudgetCertificate.controlled,
      sampleFiniteCycleSubstitutionModelsBudgetCertificate]
  · norm_num [FiniteCycleSubstitutionModelsBudgetCertificate.budgetControlled,
      sampleFiniteCycleSubstitutionModelsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleFiniteCycleSubstitutionModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleFiniteCycleSubstitutionModelsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleFiniteCycleSubstitutionModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [FiniteCycleSubstitutionModelsBudgetCertificate.controlled,
      sampleFiniteCycleSubstitutionModelsBudgetCertificate]
  · norm_num [FiniteCycleSubstitutionModelsBudgetCertificate.budgetControlled,
      sampleFiniteCycleSubstitutionModelsBudgetCertificate]

example :
    sampleFiniteCycleSubstitutionModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleFiniteCycleSubstitutionModelsBudgetCertificate.size := by
  apply finiteCycleSubstitutionModels_budgetCertificate_le_size
  constructor
  · norm_num [FiniteCycleSubstitutionModelsBudgetCertificate.controlled,
      sampleFiniteCycleSubstitutionModelsBudgetCertificate]
  · norm_num [FiniteCycleSubstitutionModelsBudgetCertificate.budgetControlled,
      sampleFiniteCycleSubstitutionModelsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady
    (data : List FiniteCycleSubstitutionModelsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleFiniteCycleSubstitutionModelsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleFiniteCycleSubstitutionModelsBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppA.FiniteCycleSubstitutionModels
