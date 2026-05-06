import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Supercritical window schemas.

This module isolates a finite supercritical-window schema: a positive
critical radius controls overflow scale with perturbation slack.
-/

namespace AnalyticCombinatorics.PartB.Ch7.SupercriticalWindowSchemas

structure SupercriticalWindowData where
  criticalRadius : ℕ
  overflowScale : ℕ
  perturbationSlack : ℕ
deriving DecidableEq, Repr

def hasCriticalRadius (d : SupercriticalWindowData) : Prop :=
  0 < d.criticalRadius

def overflowScaleControlled (d : SupercriticalWindowData) : Prop :=
  d.overflowScale ≤ d.criticalRadius + d.perturbationSlack

def supercriticalWindowReady (d : SupercriticalWindowData) : Prop :=
  hasCriticalRadius d ∧ overflowScaleControlled d

def supercriticalWindowBudget (d : SupercriticalWindowData) : ℕ :=
  d.criticalRadius + d.overflowScale + d.perturbationSlack

theorem supercriticalWindowReady.hasCriticalRadius
    {d : SupercriticalWindowData}
    (h : supercriticalWindowReady d) :
    hasCriticalRadius d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem overflowScale_le_budget (d : SupercriticalWindowData) :
    d.overflowScale ≤ supercriticalWindowBudget d := by
  unfold supercriticalWindowBudget
  omega

def sampleSupercriticalWindowData : SupercriticalWindowData :=
  { criticalRadius := 6, overflowScale := 8, perturbationSlack := 3 }

example : supercriticalWindowReady sampleSupercriticalWindowData := by
  norm_num [supercriticalWindowReady, hasCriticalRadius]
  norm_num [overflowScaleControlled, sampleSupercriticalWindowData]

example : supercriticalWindowBudget sampleSupercriticalWindowData = 17 := by
  native_decide

structure SupercriticalWindowBudgetCertificate where
  criticalRadiusWindow : ℕ
  overflowScaleWindow : ℕ
  perturbationSlackWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def SupercriticalWindowBudgetCertificate.controlled
    (c : SupercriticalWindowBudgetCertificate) : Prop :=
  0 < c.criticalRadiusWindow ∧
    c.overflowScaleWindow ≤
      c.criticalRadiusWindow + c.perturbationSlackWindow + c.slack

def SupercriticalWindowBudgetCertificate.budgetControlled
    (c : SupercriticalWindowBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.criticalRadiusWindow + c.overflowScaleWindow + c.perturbationSlackWindow +
      c.slack

def SupercriticalWindowBudgetCertificate.Ready
    (c : SupercriticalWindowBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def SupercriticalWindowBudgetCertificate.size
    (c : SupercriticalWindowBudgetCertificate) : ℕ :=
  c.criticalRadiusWindow + c.overflowScaleWindow + c.perturbationSlackWindow +
    c.slack

theorem supercriticalWindow_budgetCertificate_le_size
    (c : SupercriticalWindowBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleSupercriticalWindowBudgetCertificate :
    SupercriticalWindowBudgetCertificate :=
  { criticalRadiusWindow := 6
    overflowScaleWindow := 8
    perturbationSlackWindow := 3
    certificateBudgetWindow := 18
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleSupercriticalWindowBudgetCertificate.Ready := by
  constructor
  · norm_num [SupercriticalWindowBudgetCertificate.controlled,
      sampleSupercriticalWindowBudgetCertificate]
  · norm_num [SupercriticalWindowBudgetCertificate.budgetControlled,
      sampleSupercriticalWindowBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleSupercriticalWindowBudgetCertificate.certificateBudgetWindow ≤
      sampleSupercriticalWindowBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleSupercriticalWindowBudgetCertificate.Ready := by
  constructor
  · norm_num [SupercriticalWindowBudgetCertificate.controlled,
      sampleSupercriticalWindowBudgetCertificate]
  · norm_num [SupercriticalWindowBudgetCertificate.budgetControlled,
      sampleSupercriticalWindowBudgetCertificate]

example :
    sampleSupercriticalWindowBudgetCertificate.certificateBudgetWindow ≤
      sampleSupercriticalWindowBudgetCertificate.size := by
  apply supercriticalWindow_budgetCertificate_le_size
  constructor
  · norm_num [SupercriticalWindowBudgetCertificate.controlled,
      sampleSupercriticalWindowBudgetCertificate]
  · norm_num [SupercriticalWindowBudgetCertificate.budgetControlled,
      sampleSupercriticalWindowBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List SupercriticalWindowBudgetCertificate) : Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady [sampleSupercriticalWindowBudgetCertificate] = true := by
  unfold budgetCertificateListReady sampleSupercriticalWindowBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch7.SupercriticalWindowSchemas
