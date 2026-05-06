import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Uniform Schwarz reflection window models.

This module records finite bookkeeping for Schwarz reflection windows.
-/

namespace AnalyticCombinatorics.AppB.UniformSchwarzReflectionWindowModels

structure SchwarzReflectionWindowData where
  reflectionArcs : ℕ
  continuationWindow : ℕ
  reflectionSlack : ℕ
deriving DecidableEq, Repr

def hasReflectionArcs (d : SchwarzReflectionWindowData) : Prop :=
  0 < d.reflectionArcs

def continuationWindowControlled (d : SchwarzReflectionWindowData) : Prop :=
  d.continuationWindow ≤ d.reflectionArcs + d.reflectionSlack

def schwarzReflectionReady (d : SchwarzReflectionWindowData) : Prop :=
  hasReflectionArcs d ∧ continuationWindowControlled d

def schwarzReflectionBudget (d : SchwarzReflectionWindowData) : ℕ :=
  d.reflectionArcs + d.continuationWindow + d.reflectionSlack

theorem schwarzReflectionReady.hasReflectionArcs
    {d : SchwarzReflectionWindowData}
    (h : schwarzReflectionReady d) :
    hasReflectionArcs d ∧ continuationWindowControlled d ∧
      d.continuationWindow ≤ schwarzReflectionBudget d := by
  refine ⟨h.1, h.2, ?_⟩
  unfold schwarzReflectionBudget
  omega

theorem continuationWindow_le_budget (d : SchwarzReflectionWindowData) :
    d.continuationWindow ≤ schwarzReflectionBudget d := by
  unfold schwarzReflectionBudget
  omega

def sampleSchwarzReflectionWindowData : SchwarzReflectionWindowData :=
  { reflectionArcs := 6, continuationWindow := 8, reflectionSlack := 3 }

example : schwarzReflectionReady sampleSchwarzReflectionWindowData := by
  norm_num [schwarzReflectionReady, hasReflectionArcs]
  norm_num [continuationWindowControlled, sampleSchwarzReflectionWindowData]

example : schwarzReflectionBudget sampleSchwarzReflectionWindowData = 17 := by
  native_decide

/-- Finite executable readiness audit for Schwarz reflection windows. -/
def schwarzReflectionListReady (windows : List SchwarzReflectionWindowData) : Bool :=
  windows.all fun d =>
    0 < d.reflectionArcs &&
      d.continuationWindow ≤ d.reflectionArcs + d.reflectionSlack

theorem schwarzReflectionList_readyWindow :
    schwarzReflectionListReady
      [{ reflectionArcs := 4, continuationWindow := 5, reflectionSlack := 1 },
       { reflectionArcs := 6, continuationWindow := 8, reflectionSlack := 3 }] = true := by
  unfold schwarzReflectionListReady
  native_decide


structure UniformSchwarzReflectionWindowModelsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def UniformSchwarzReflectionWindowModelsBudgetCertificate.controlled
    (c : UniformSchwarzReflectionWindowModelsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def UniformSchwarzReflectionWindowModelsBudgetCertificate.budgetControlled
    (c : UniformSchwarzReflectionWindowModelsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def UniformSchwarzReflectionWindowModelsBudgetCertificate.Ready
    (c : UniformSchwarzReflectionWindowModelsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def UniformSchwarzReflectionWindowModelsBudgetCertificate.size
    (c : UniformSchwarzReflectionWindowModelsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem uniformSchwarzReflectionWindowModels_budgetCertificate_le_size
    (c : UniformSchwarzReflectionWindowModelsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleUniformSchwarzReflectionWindowModelsBudgetCertificate :
    UniformSchwarzReflectionWindowModelsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleUniformSchwarzReflectionWindowModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [UniformSchwarzReflectionWindowModelsBudgetCertificate.controlled,
      sampleUniformSchwarzReflectionWindowModelsBudgetCertificate]
  · norm_num [UniformSchwarzReflectionWindowModelsBudgetCertificate.budgetControlled,
      sampleUniformSchwarzReflectionWindowModelsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleUniformSchwarzReflectionWindowModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleUniformSchwarzReflectionWindowModelsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleUniformSchwarzReflectionWindowModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [UniformSchwarzReflectionWindowModelsBudgetCertificate.controlled,
      sampleUniformSchwarzReflectionWindowModelsBudgetCertificate]
  · norm_num [UniformSchwarzReflectionWindowModelsBudgetCertificate.budgetControlled,
      sampleUniformSchwarzReflectionWindowModelsBudgetCertificate]

example :
    sampleUniformSchwarzReflectionWindowModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleUniformSchwarzReflectionWindowModelsBudgetCertificate.size := by
  apply uniformSchwarzReflectionWindowModels_budgetCertificate_le_size
  constructor
  · norm_num [UniformSchwarzReflectionWindowModelsBudgetCertificate.controlled,
      sampleUniformSchwarzReflectionWindowModelsBudgetCertificate]
  · norm_num [UniformSchwarzReflectionWindowModelsBudgetCertificate.budgetControlled,
      sampleUniformSchwarzReflectionWindowModelsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady
    (data : List UniformSchwarzReflectionWindowModelsBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleUniformSchwarzReflectionWindowModelsBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleUniformSchwarzReflectionWindowModelsBudgetCertificate
  native_decide
end AnalyticCombinatorics.AppB.UniformSchwarzReflectionWindowModels
