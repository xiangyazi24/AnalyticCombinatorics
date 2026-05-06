import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Size-bias coupling schemas.

This module records finite bookkeeping for size-bias couplings.
-/

namespace AnalyticCombinatorics.AppC.SizeBiasCouplingSchemas

structure SizeBiasCouplingData where
  biasScale : ℕ
  couplingWindow : ℕ
  biasSlack : ℕ
deriving DecidableEq, Repr

def hasBiasScale (d : SizeBiasCouplingData) : Prop :=
  0 < d.biasScale

def couplingWindowControlled (d : SizeBiasCouplingData) : Prop :=
  d.couplingWindow ≤ d.biasScale + d.biasSlack

def sizeBiasCouplingReady (d : SizeBiasCouplingData) : Prop :=
  hasBiasScale d ∧ couplingWindowControlled d

def sizeBiasCouplingBudget (d : SizeBiasCouplingData) : ℕ :=
  d.biasScale + d.couplingWindow + d.biasSlack

theorem sizeBiasCouplingReady.hasBiasScale {d : SizeBiasCouplingData}
    (h : sizeBiasCouplingReady d) :
    hasBiasScale d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem couplingWindow_le_budget (d : SizeBiasCouplingData) :
    d.couplingWindow ≤ sizeBiasCouplingBudget d := by
  unfold sizeBiasCouplingBudget
  omega

def sampleSizeBiasCouplingData : SizeBiasCouplingData :=
  { biasScale := 6, couplingWindow := 8, biasSlack := 3 }

example : sizeBiasCouplingReady sampleSizeBiasCouplingData := by
  norm_num [sizeBiasCouplingReady, hasBiasScale]
  norm_num [couplingWindowControlled, sampleSizeBiasCouplingData]

example : sizeBiasCouplingBudget sampleSizeBiasCouplingData = 17 := by
  native_decide

structure SizeBiasCouplingWindow where
  biasScale : ℕ
  couplingWindow : ℕ
  biasSlack : ℕ
  transferBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def SizeBiasCouplingWindow.couplingControlled (w : SizeBiasCouplingWindow) : Prop :=
  w.couplingWindow ≤ w.biasScale + w.biasSlack + w.slack

def SizeBiasCouplingWindow.transferControlled (w : SizeBiasCouplingWindow) : Prop :=
  w.transferBudget ≤ w.biasScale + w.couplingWindow + w.biasSlack + w.slack

def sizeBiasCouplingWindowReady (w : SizeBiasCouplingWindow) : Prop :=
  0 < w.biasScale ∧
    w.couplingControlled ∧
    w.transferControlled

def SizeBiasCouplingWindow.certificate (w : SizeBiasCouplingWindow) : ℕ :=
  w.biasScale + w.couplingWindow + w.biasSlack + w.slack

theorem sizeBiasCoupling_transferBudget_le_certificate {w : SizeBiasCouplingWindow}
    (h : sizeBiasCouplingWindowReady w) :
    w.transferBudget ≤ w.certificate := by
  rcases h with ⟨_, _, htransfer⟩
  exact htransfer

def sampleSizeBiasCouplingWindow : SizeBiasCouplingWindow :=
  { biasScale := 6, couplingWindow := 8, biasSlack := 3, transferBudget := 16, slack := 0 }

example : sizeBiasCouplingWindowReady sampleSizeBiasCouplingWindow := by
  norm_num [sizeBiasCouplingWindowReady, SizeBiasCouplingWindow.couplingControlled,
    SizeBiasCouplingWindow.transferControlled, sampleSizeBiasCouplingWindow]

example : sampleSizeBiasCouplingWindow.certificate = 17 := by
  native_decide


structure SizeBiasCouplingSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def SizeBiasCouplingSchemasBudgetCertificate.controlled
    (c : SizeBiasCouplingSchemasBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def SizeBiasCouplingSchemasBudgetCertificate.budgetControlled
    (c : SizeBiasCouplingSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def SizeBiasCouplingSchemasBudgetCertificate.Ready
    (c : SizeBiasCouplingSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def SizeBiasCouplingSchemasBudgetCertificate.size
    (c : SizeBiasCouplingSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem sizeBiasCouplingSchemas_budgetCertificate_le_size
    (c : SizeBiasCouplingSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleSizeBiasCouplingSchemasBudgetCertificate :
    SizeBiasCouplingSchemasBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleSizeBiasCouplingSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [SizeBiasCouplingSchemasBudgetCertificate.controlled,
      sampleSizeBiasCouplingSchemasBudgetCertificate]
  · norm_num [SizeBiasCouplingSchemasBudgetCertificate.budgetControlled,
      sampleSizeBiasCouplingSchemasBudgetCertificate]

example : sampleSizeBiasCouplingSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [SizeBiasCouplingSchemasBudgetCertificate.controlled,
      sampleSizeBiasCouplingSchemasBudgetCertificate]
  · norm_num [SizeBiasCouplingSchemasBudgetCertificate.budgetControlled,
      sampleSizeBiasCouplingSchemasBudgetCertificate]

example :
    sampleSizeBiasCouplingSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleSizeBiasCouplingSchemasBudgetCertificate.size := by
  apply sizeBiasCouplingSchemas_budgetCertificate_le_size
  constructor
  · norm_num [SizeBiasCouplingSchemasBudgetCertificate.controlled,
      sampleSizeBiasCouplingSchemasBudgetCertificate]
  · norm_num [SizeBiasCouplingSchemasBudgetCertificate.budgetControlled,
      sampleSizeBiasCouplingSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_le_size :
    sampleSizeBiasCouplingSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleSizeBiasCouplingSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List SizeBiasCouplingSchemasBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleSizeBiasCouplingSchemasBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleSizeBiasCouplingSchemasBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppC.SizeBiasCouplingSchemas
