import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Local dependence coupling schemas.

This module records finite bookkeeping for local dependence couplings.
-/

namespace AnalyticCombinatorics.AppC.LocalDependenceCouplingSchemas

structure LocalDependenceCouplingData where
  dependenceRadius : ℕ
  couplingWindow : ℕ
  localitySlack : ℕ
deriving DecidableEq, Repr

def hasDependenceRadius (d : LocalDependenceCouplingData) : Prop :=
  0 < d.dependenceRadius

def couplingWindowControlled (d : LocalDependenceCouplingData) : Prop :=
  d.couplingWindow ≤ d.dependenceRadius + d.localitySlack

def localDependenceCouplingReady
    (d : LocalDependenceCouplingData) : Prop :=
  hasDependenceRadius d ∧ couplingWindowControlled d

def localDependenceCouplingBudget
    (d : LocalDependenceCouplingData) : ℕ :=
  d.dependenceRadius + d.couplingWindow + d.localitySlack

theorem localDependenceCouplingReady.hasDependenceRadius
    {d : LocalDependenceCouplingData}
    (h : localDependenceCouplingReady d) :
    hasDependenceRadius d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem couplingWindow_le_budget (d : LocalDependenceCouplingData) :
    d.couplingWindow ≤ localDependenceCouplingBudget d := by
  unfold localDependenceCouplingBudget
  omega

def sampleLocalDependenceCouplingData : LocalDependenceCouplingData :=
  { dependenceRadius := 6, couplingWindow := 8, localitySlack := 3 }

example : localDependenceCouplingReady
    sampleLocalDependenceCouplingData := by
  norm_num [localDependenceCouplingReady, hasDependenceRadius]
  norm_num [couplingWindowControlled, sampleLocalDependenceCouplingData]

example :
    localDependenceCouplingBudget sampleLocalDependenceCouplingData = 17 := by
  native_decide

structure LocalDependenceCouplingWindow where
  radiusWindow : ℕ
  couplingWindow : ℕ
  localitySlack : ℕ
  couplingBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def LocalDependenceCouplingWindow.couplingControlled
    (w : LocalDependenceCouplingWindow) : Prop :=
  w.couplingWindow ≤ w.radiusWindow + w.localitySlack + w.slack

def localDependenceCouplingWindowReady
    (w : LocalDependenceCouplingWindow) : Prop :=
  0 < w.radiusWindow ∧ w.couplingControlled ∧
    w.couplingBudget ≤ w.radiusWindow + w.couplingWindow + w.slack

def LocalDependenceCouplingWindow.certificate
    (w : LocalDependenceCouplingWindow) : ℕ :=
  w.radiusWindow + w.couplingWindow + w.localitySlack + w.couplingBudget + w.slack

theorem localDependenceCoupling_couplingBudget_le_certificate
    (w : LocalDependenceCouplingWindow) :
    w.couplingBudget ≤ w.certificate := by
  unfold LocalDependenceCouplingWindow.certificate
  omega

def sampleLocalDependenceCouplingWindow : LocalDependenceCouplingWindow :=
  { radiusWindow := 5, couplingWindow := 7, localitySlack := 2,
    couplingBudget := 14, slack := 2 }

example : localDependenceCouplingWindowReady
    sampleLocalDependenceCouplingWindow := by
  norm_num [localDependenceCouplingWindowReady,
    LocalDependenceCouplingWindow.couplingControlled, sampleLocalDependenceCouplingWindow]


structure LocalDependenceCouplingSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def LocalDependenceCouplingSchemasBudgetCertificate.controlled
    (c : LocalDependenceCouplingSchemasBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def LocalDependenceCouplingSchemasBudgetCertificate.budgetControlled
    (c : LocalDependenceCouplingSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def LocalDependenceCouplingSchemasBudgetCertificate.Ready
    (c : LocalDependenceCouplingSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def LocalDependenceCouplingSchemasBudgetCertificate.size
    (c : LocalDependenceCouplingSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem localDependenceCouplingSchemas_budgetCertificate_le_size
    (c : LocalDependenceCouplingSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleLocalDependenceCouplingSchemasBudgetCertificate :
    LocalDependenceCouplingSchemasBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleLocalDependenceCouplingSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [LocalDependenceCouplingSchemasBudgetCertificate.controlled,
      sampleLocalDependenceCouplingSchemasBudgetCertificate]
  · norm_num [LocalDependenceCouplingSchemasBudgetCertificate.budgetControlled,
      sampleLocalDependenceCouplingSchemasBudgetCertificate]

example : sampleLocalDependenceCouplingSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [LocalDependenceCouplingSchemasBudgetCertificate.controlled,
      sampleLocalDependenceCouplingSchemasBudgetCertificate]
  · norm_num [LocalDependenceCouplingSchemasBudgetCertificate.budgetControlled,
      sampleLocalDependenceCouplingSchemasBudgetCertificate]

example :
    sampleLocalDependenceCouplingSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleLocalDependenceCouplingSchemasBudgetCertificate.size := by
  apply localDependenceCouplingSchemas_budgetCertificate_le_size
  constructor
  · norm_num [LocalDependenceCouplingSchemasBudgetCertificate.controlled,
      sampleLocalDependenceCouplingSchemasBudgetCertificate]
  · norm_num [LocalDependenceCouplingSchemasBudgetCertificate.budgetControlled,
      sampleLocalDependenceCouplingSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_le_size :
    sampleLocalDependenceCouplingSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleLocalDependenceCouplingSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady
    (data : List LocalDependenceCouplingSchemasBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleLocalDependenceCouplingSchemasBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleLocalDependenceCouplingSchemasBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppC.LocalDependenceCouplingSchemas
