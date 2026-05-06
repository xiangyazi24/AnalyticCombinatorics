import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Cycle index window schemas.

This module records a finite cycle-index window schema where a positive
cycle count controls an orbit window with symmetry slack.
-/

namespace AnalyticCombinatorics.PartA.Ch2.CycleIndexWindowSchemas

structure CycleIndexWindowData where
  cycleCount : ℕ
  orbitWindow : ℕ
  symmetrySlack : ℕ
deriving DecidableEq, Repr

def hasCycleCount (d : CycleIndexWindowData) : Prop :=
  0 < d.cycleCount

def orbitWindowControlled (d : CycleIndexWindowData) : Prop :=
  d.orbitWindow ≤ d.cycleCount + d.symmetrySlack

def cycleIndexWindowReady (d : CycleIndexWindowData) : Prop :=
  hasCycleCount d ∧ orbitWindowControlled d

def cycleIndexWindowBudget (d : CycleIndexWindowData) : ℕ :=
  d.cycleCount + d.orbitWindow + d.symmetrySlack

theorem cycleIndexWindowReady.hasCycleCount {d : CycleIndexWindowData}
    (h : cycleIndexWindowReady d) :
    hasCycleCount d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem orbitWindow_le_budget (d : CycleIndexWindowData) :
    d.orbitWindow ≤ cycleIndexWindowBudget d := by
  unfold cycleIndexWindowBudget
  omega

def sampleCycleIndexWindowData : CycleIndexWindowData :=
  { cycleCount := 6, orbitWindow := 8, symmetrySlack := 3 }

example : cycleIndexWindowReady sampleCycleIndexWindowData := by
  norm_num [cycleIndexWindowReady, hasCycleCount]
  norm_num [orbitWindowControlled, sampleCycleIndexWindowData]

example : cycleIndexWindowBudget sampleCycleIndexWindowData = 17 := by
  native_decide

structure CycleIndexWindowBudgetCertificate where
  cycleWindow : ℕ
  orbitWindow : ℕ
  symmetrySlackWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def CycleIndexWindowBudgetCertificate.controlled
    (c : CycleIndexWindowBudgetCertificate) : Prop :=
  0 < c.cycleWindow ∧
    c.orbitWindow ≤ c.cycleWindow + c.symmetrySlackWindow + c.slack

def CycleIndexWindowBudgetCertificate.budgetControlled
    (c : CycleIndexWindowBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.cycleWindow + c.orbitWindow + c.symmetrySlackWindow + c.slack

def CycleIndexWindowBudgetCertificate.Ready
    (c : CycleIndexWindowBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def CycleIndexWindowBudgetCertificate.size
    (c : CycleIndexWindowBudgetCertificate) : ℕ :=
  c.cycleWindow + c.orbitWindow + c.symmetrySlackWindow + c.slack

theorem cycleIndexWindow_budgetCertificate_le_size
    (c : CycleIndexWindowBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleCycleIndexWindowBudgetCertificate :
    CycleIndexWindowBudgetCertificate :=
  { cycleWindow := 6
    orbitWindow := 8
    symmetrySlackWindow := 3
    certificateBudgetWindow := 18
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleCycleIndexWindowBudgetCertificate.Ready := by
  constructor
  · norm_num [CycleIndexWindowBudgetCertificate.controlled,
      sampleCycleIndexWindowBudgetCertificate]
  · norm_num [CycleIndexWindowBudgetCertificate.budgetControlled,
      sampleCycleIndexWindowBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleCycleIndexWindowBudgetCertificate.certificateBudgetWindow ≤
      sampleCycleIndexWindowBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleCycleIndexWindowBudgetCertificate.Ready := by
  constructor
  · norm_num [CycleIndexWindowBudgetCertificate.controlled,
      sampleCycleIndexWindowBudgetCertificate]
  · norm_num [CycleIndexWindowBudgetCertificate.budgetControlled,
      sampleCycleIndexWindowBudgetCertificate]

example :
    sampleCycleIndexWindowBudgetCertificate.certificateBudgetWindow ≤
      sampleCycleIndexWindowBudgetCertificate.size := by
  apply cycleIndexWindow_budgetCertificate_le_size
  constructor
  · norm_num [CycleIndexWindowBudgetCertificate.controlled,
      sampleCycleIndexWindowBudgetCertificate]
  · norm_num [CycleIndexWindowBudgetCertificate.budgetControlled,
      sampleCycleIndexWindowBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List CycleIndexWindowBudgetCertificate) : Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady [sampleCycleIndexWindowBudgetCertificate] = true := by
  unfold budgetCertificateListReady sampleCycleIndexWindowBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartA.Ch2.CycleIndexWindowSchemas
