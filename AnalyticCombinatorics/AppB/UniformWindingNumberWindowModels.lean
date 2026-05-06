import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Uniform winding number window models.

This module records finite bookkeeping for winding number windows.
-/

namespace AnalyticCombinatorics.AppB.UniformWindingNumberWindowModels

structure WindingNumberWindowData where
  windingScale : ℕ
  windingWindow : ℕ
  homotopySlack : ℕ
deriving DecidableEq, Repr

def hasWindingScale (d : WindingNumberWindowData) : Prop :=
  0 < d.windingScale

def windingWindowControlled (d : WindingNumberWindowData) : Prop :=
  d.windingWindow ≤ d.windingScale + d.homotopySlack

def windingNumberWindowReady (d : WindingNumberWindowData) : Prop :=
  hasWindingScale d ∧ windingWindowControlled d

def windingNumberWindowBudget (d : WindingNumberWindowData) : ℕ :=
  d.windingScale + d.windingWindow + d.homotopySlack

theorem windingNumberWindowReady.hasWindingScale
    {d : WindingNumberWindowData}
    (h : windingNumberWindowReady d) :
    hasWindingScale d ∧ windingWindowControlled d ∧
      d.windingWindow ≤ windingNumberWindowBudget d := by
  refine ⟨h.1, h.2, ?_⟩
  unfold windingNumberWindowBudget
  omega

theorem windingWindow_le_budget (d : WindingNumberWindowData) :
    d.windingWindow ≤ windingNumberWindowBudget d := by
  unfold windingNumberWindowBudget
  omega

def sampleWindingNumberWindowData : WindingNumberWindowData :=
  { windingScale := 6, windingWindow := 8, homotopySlack := 3 }

example : windingNumberWindowReady sampleWindingNumberWindowData := by
  norm_num [windingNumberWindowReady, hasWindingScale]
  norm_num [windingWindowControlled, sampleWindingNumberWindowData]

example : windingNumberWindowBudget sampleWindingNumberWindowData = 17 := by
  native_decide

/-- Finite executable readiness audit for uniform winding-number windows. -/
def windingNumberWindowListReady (windows : List WindingNumberWindowData) : Bool :=
  windows.all fun d =>
    0 < d.windingScale && d.windingWindow ≤ d.windingScale + d.homotopySlack

theorem windingNumberWindowList_readyWindow :
    windingNumberWindowListReady
      [{ windingScale := 4, windingWindow := 5, homotopySlack := 1 },
       { windingScale := 6, windingWindow := 8, homotopySlack := 3 }] = true := by
  unfold windingNumberWindowListReady
  native_decide


structure UniformWindingNumberWindowModelsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def UniformWindingNumberWindowModelsBudgetCertificate.controlled
    (c : UniformWindingNumberWindowModelsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def UniformWindingNumberWindowModelsBudgetCertificate.budgetControlled
    (c : UniformWindingNumberWindowModelsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def UniformWindingNumberWindowModelsBudgetCertificate.Ready
    (c : UniformWindingNumberWindowModelsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def UniformWindingNumberWindowModelsBudgetCertificate.size
    (c : UniformWindingNumberWindowModelsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem uniformWindingNumberWindowModels_budgetCertificate_le_size
    (c : UniformWindingNumberWindowModelsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleUniformWindingNumberWindowModelsBudgetCertificate :
    UniformWindingNumberWindowModelsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleUniformWindingNumberWindowModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [UniformWindingNumberWindowModelsBudgetCertificate.controlled,
      sampleUniformWindingNumberWindowModelsBudgetCertificate]
  · norm_num [UniformWindingNumberWindowModelsBudgetCertificate.budgetControlled,
      sampleUniformWindingNumberWindowModelsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleUniformWindingNumberWindowModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleUniformWindingNumberWindowModelsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleUniformWindingNumberWindowModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [UniformWindingNumberWindowModelsBudgetCertificate.controlled,
      sampleUniformWindingNumberWindowModelsBudgetCertificate]
  · norm_num [UniformWindingNumberWindowModelsBudgetCertificate.budgetControlled,
      sampleUniformWindingNumberWindowModelsBudgetCertificate]

example :
    sampleUniformWindingNumberWindowModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleUniformWindingNumberWindowModelsBudgetCertificate.size := by
  apply uniformWindingNumberWindowModels_budgetCertificate_le_size
  constructor
  · norm_num [UniformWindingNumberWindowModelsBudgetCertificate.controlled,
      sampleUniformWindingNumberWindowModelsBudgetCertificate]
  · norm_num [UniformWindingNumberWindowModelsBudgetCertificate.budgetControlled,
      sampleUniformWindingNumberWindowModelsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady
    (data : List UniformWindingNumberWindowModelsBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleUniformWindingNumberWindowModelsBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleUniformWindingNumberWindowModelsBudgetCertificate
  native_decide
end AnalyticCombinatorics.AppB.UniformWindingNumberWindowModels
