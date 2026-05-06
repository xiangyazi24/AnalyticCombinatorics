import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Local dependence limit schemas.

This module records finite bookkeeping for local dependence limits.
-/

namespace AnalyticCombinatorics.AppC.LocalDependenceLimitSchemas

structure LocalDependenceData where
  dependencyRadius : ℕ
  neighborhoodSize : ℕ
  limitSlack : ℕ
deriving DecidableEq, Repr

def hasDependencyRadius (d : LocalDependenceData) : Prop :=
  0 < d.dependencyRadius

def neighborhoodSizeControlled (d : LocalDependenceData) : Prop :=
  d.neighborhoodSize ≤ d.dependencyRadius + d.limitSlack

def localDependenceReady (d : LocalDependenceData) : Prop :=
  hasDependencyRadius d ∧ neighborhoodSizeControlled d

def localDependenceBudget (d : LocalDependenceData) : ℕ :=
  d.dependencyRadius + d.neighborhoodSize + d.limitSlack

theorem localDependenceReady.hasDependencyRadius {d : LocalDependenceData}
    (h : localDependenceReady d) :
    hasDependencyRadius d ∧ neighborhoodSizeControlled d ∧
      d.neighborhoodSize ≤ localDependenceBudget d := by
  refine ⟨h.1, h.2, ?_⟩
  unfold localDependenceBudget
  omega

theorem neighborhoodSize_le_budget (d : LocalDependenceData) :
    d.neighborhoodSize ≤ localDependenceBudget d := by
  unfold localDependenceBudget
  omega

def sampleLocalDependenceData : LocalDependenceData :=
  { dependencyRadius := 6, neighborhoodSize := 8, limitSlack := 3 }

example : localDependenceReady sampleLocalDependenceData := by
  norm_num [localDependenceReady, hasDependencyRadius]
  norm_num [neighborhoodSizeControlled, sampleLocalDependenceData]

example : localDependenceBudget sampleLocalDependenceData = 17 := by
  native_decide

structure LocalDependenceLimitWindow where
  radiusWindow : ℕ
  neighborhoodWindow : ℕ
  limitSlack : ℕ
  localBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def LocalDependenceLimitWindow.neighborhoodControlled
    (w : LocalDependenceLimitWindow) : Prop :=
  w.neighborhoodWindow ≤ w.radiusWindow + w.limitSlack + w.slack

def localDependenceLimitWindowReady (w : LocalDependenceLimitWindow) : Prop :=
  0 < w.radiusWindow ∧ w.neighborhoodControlled ∧
    w.localBudget ≤ w.radiusWindow + w.neighborhoodWindow + w.slack

def LocalDependenceLimitWindow.certificate (w : LocalDependenceLimitWindow) : ℕ :=
  w.radiusWindow + w.neighborhoodWindow + w.limitSlack + w.localBudget + w.slack

theorem localDependenceLimit_localBudget_le_certificate
    (w : LocalDependenceLimitWindow) :
    w.localBudget ≤ w.certificate := by
  unfold LocalDependenceLimitWindow.certificate
  omega

def sampleLocalDependenceLimitWindow : LocalDependenceLimitWindow :=
  { radiusWindow := 5, neighborhoodWindow := 7, limitSlack := 2, localBudget := 14, slack := 2 }

example : localDependenceLimitWindowReady sampleLocalDependenceLimitWindow := by
  norm_num [localDependenceLimitWindowReady,
    LocalDependenceLimitWindow.neighborhoodControlled, sampleLocalDependenceLimitWindow]


structure LocalDependenceLimitSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def LocalDependenceLimitSchemasBudgetCertificate.controlled
    (c : LocalDependenceLimitSchemasBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def LocalDependenceLimitSchemasBudgetCertificate.budgetControlled
    (c : LocalDependenceLimitSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def LocalDependenceLimitSchemasBudgetCertificate.Ready
    (c : LocalDependenceLimitSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def LocalDependenceLimitSchemasBudgetCertificate.size
    (c : LocalDependenceLimitSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem localDependenceLimitSchemas_budgetCertificate_le_size
    (c : LocalDependenceLimitSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleLocalDependenceLimitSchemasBudgetCertificate :
    LocalDependenceLimitSchemasBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleLocalDependenceLimitSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [LocalDependenceLimitSchemasBudgetCertificate.controlled,
      sampleLocalDependenceLimitSchemasBudgetCertificate]
  · norm_num [LocalDependenceLimitSchemasBudgetCertificate.budgetControlled,
      sampleLocalDependenceLimitSchemasBudgetCertificate]

example : sampleLocalDependenceLimitSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [LocalDependenceLimitSchemasBudgetCertificate.controlled,
      sampleLocalDependenceLimitSchemasBudgetCertificate]
  · norm_num [LocalDependenceLimitSchemasBudgetCertificate.budgetControlled,
      sampleLocalDependenceLimitSchemasBudgetCertificate]

example :
    sampleLocalDependenceLimitSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleLocalDependenceLimitSchemasBudgetCertificate.size := by
  apply localDependenceLimitSchemas_budgetCertificate_le_size
  constructor
  · norm_num [LocalDependenceLimitSchemasBudgetCertificate.controlled,
      sampleLocalDependenceLimitSchemasBudgetCertificate]
  · norm_num [LocalDependenceLimitSchemasBudgetCertificate.budgetControlled,
      sampleLocalDependenceLimitSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_le_size :
    sampleLocalDependenceLimitSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleLocalDependenceLimitSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List LocalDependenceLimitSchemasBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleLocalDependenceLimitSchemasBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleLocalDependenceLimitSchemasBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppC.LocalDependenceLimitSchemas
