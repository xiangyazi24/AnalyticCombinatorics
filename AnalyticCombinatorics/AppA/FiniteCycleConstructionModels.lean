import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Finite cycle construction models.

This module gives a finite schema for cycle constructions with a nonempty
cycle slot count and a rotation budget bounded by symmetry slack.
-/

namespace AnalyticCombinatorics.AppA.FiniteCycleConstructionModels

structure CycleConstructionData where
  cycleSlots : ℕ
  rotationBudget : ℕ
  symmetrySlack : ℕ
deriving DecidableEq, Repr

def hasCycleSlot (d : CycleConstructionData) : Prop :=
  0 < d.cycleSlots

def rotationsControlled (d : CycleConstructionData) : Prop :=
  d.rotationBudget ≤ d.cycleSlots + d.symmetrySlack

def cycleConstructionReady (d : CycleConstructionData) : Prop :=
  hasCycleSlot d ∧ rotationsControlled d

def cycleConstructionBudget (d : CycleConstructionData) : ℕ :=
  d.cycleSlots + d.rotationBudget + d.symmetrySlack

theorem cycleConstructionReady.hasCycleSlot {d : CycleConstructionData}
    (h : cycleConstructionReady d) :
    hasCycleSlot d ∧ rotationsControlled d ∧ d.rotationBudget ≤ cycleConstructionBudget d := by
  refine ⟨h.1, h.2, ?_⟩
  unfold cycleConstructionBudget
  omega

theorem rotationBudget_le_budget (d : CycleConstructionData) :
    d.rotationBudget ≤ cycleConstructionBudget d := by
  unfold cycleConstructionBudget
  omega

def sampleCycleConstructionData : CycleConstructionData :=
  { cycleSlots := 5, rotationBudget := 7, symmetrySlack := 3 }

example : cycleConstructionReady sampleCycleConstructionData := by
  norm_num [cycleConstructionReady, hasCycleSlot]
  norm_num [rotationsControlled, sampleCycleConstructionData]

example : cycleConstructionBudget sampleCycleConstructionData = 15 := by
  native_decide

structure CycleConstructionWindow where
  cycleSlots : ℕ
  rotationBudget : ℕ
  symmetrySlack : ℕ
  orbitBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def CycleConstructionWindow.rotationControlled (w : CycleConstructionWindow) : Prop :=
  w.rotationBudget ≤ w.cycleSlots + w.symmetrySlack + w.slack

def CycleConstructionWindow.orbitControlled (w : CycleConstructionWindow) : Prop :=
  w.orbitBudget ≤ w.cycleSlots + w.rotationBudget + w.symmetrySlack + w.slack

def cycleConstructionWindowReady (w : CycleConstructionWindow) : Prop :=
  0 < w.cycleSlots ∧
    w.rotationControlled ∧
    w.orbitControlled

def CycleConstructionWindow.certificate (w : CycleConstructionWindow) : ℕ :=
  w.cycleSlots + w.rotationBudget + w.symmetrySlack + w.slack

theorem cycleConstruction_orbitBudget_le_certificate {w : CycleConstructionWindow}
    (h : cycleConstructionWindowReady w) :
    w.orbitBudget ≤ w.certificate := by
  rcases h with ⟨_, _, horbit⟩
  exact horbit

def sampleCycleConstructionWindow : CycleConstructionWindow :=
  { cycleSlots := 5, rotationBudget := 7, symmetrySlack := 3, orbitBudget := 14, slack := 0 }

example : cycleConstructionWindowReady sampleCycleConstructionWindow := by
  norm_num [cycleConstructionWindowReady, CycleConstructionWindow.rotationControlled,
    CycleConstructionWindow.orbitControlled, sampleCycleConstructionWindow]

example : sampleCycleConstructionWindow.certificate = 15 := by
  native_decide


structure FiniteCycleConstructionModelsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def FiniteCycleConstructionModelsBudgetCertificate.controlled
    (c : FiniteCycleConstructionModelsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def FiniteCycleConstructionModelsBudgetCertificate.budgetControlled
    (c : FiniteCycleConstructionModelsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def FiniteCycleConstructionModelsBudgetCertificate.Ready
    (c : FiniteCycleConstructionModelsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def FiniteCycleConstructionModelsBudgetCertificate.size
    (c : FiniteCycleConstructionModelsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem finiteCycleConstructionModels_budgetCertificate_le_size
    (c : FiniteCycleConstructionModelsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleFiniteCycleConstructionModelsBudgetCertificate :
    FiniteCycleConstructionModelsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleFiniteCycleConstructionModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [FiniteCycleConstructionModelsBudgetCertificate.controlled,
      sampleFiniteCycleConstructionModelsBudgetCertificate]
  · norm_num [FiniteCycleConstructionModelsBudgetCertificate.budgetControlled,
      sampleFiniteCycleConstructionModelsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleFiniteCycleConstructionModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleFiniteCycleConstructionModelsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleFiniteCycleConstructionModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [FiniteCycleConstructionModelsBudgetCertificate.controlled,
      sampleFiniteCycleConstructionModelsBudgetCertificate]
  · norm_num [FiniteCycleConstructionModelsBudgetCertificate.budgetControlled,
      sampleFiniteCycleConstructionModelsBudgetCertificate]

example :
    sampleFiniteCycleConstructionModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleFiniteCycleConstructionModelsBudgetCertificate.size := by
  apply finiteCycleConstructionModels_budgetCertificate_le_size
  constructor
  · norm_num [FiniteCycleConstructionModelsBudgetCertificate.controlled,
      sampleFiniteCycleConstructionModelsBudgetCertificate]
  · norm_num [FiniteCycleConstructionModelsBudgetCertificate.budgetControlled,
      sampleFiniteCycleConstructionModelsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady
    (data : List FiniteCycleConstructionModelsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleFiniteCycleConstructionModelsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleFiniteCycleConstructionModelsBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppA.FiniteCycleConstructionModels
