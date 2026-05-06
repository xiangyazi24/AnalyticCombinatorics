import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Tight coupling schemas.

This module records a compact arithmetic schema for tight couplings: a
positive coupling budget controls an error window with explicit tail slack.
-/

namespace AnalyticCombinatorics.AppC.TightCouplingSchemas

structure TightCouplingData where
  couplingBudget : ℕ
  errorWindow : ℕ
  tailSlack : ℕ
deriving DecidableEq, Repr

def hasCouplingBudget (d : TightCouplingData) : Prop :=
  0 < d.couplingBudget

def errorWindowControlled (d : TightCouplingData) : Prop :=
  d.errorWindow ≤ d.couplingBudget + d.tailSlack

def tightCouplingReady (d : TightCouplingData) : Prop :=
  hasCouplingBudget d ∧ errorWindowControlled d

def tightCouplingTotalBudget (d : TightCouplingData) : ℕ :=
  d.couplingBudget + d.errorWindow + d.tailSlack

theorem tightCouplingReady.hasCouplingBudget {d : TightCouplingData}
    (h : tightCouplingReady d) :
    hasCouplingBudget d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem errorWindow_le_budget (d : TightCouplingData) :
    d.errorWindow ≤ tightCouplingTotalBudget d := by
  unfold tightCouplingTotalBudget
  omega

def sampleTightCouplingData : TightCouplingData :=
  { couplingBudget := 6, errorWindow := 8, tailSlack := 3 }

example : tightCouplingReady sampleTightCouplingData := by
  norm_num [tightCouplingReady, hasCouplingBudget]
  norm_num [errorWindowControlled, sampleTightCouplingData]

example : tightCouplingTotalBudget sampleTightCouplingData = 17 := by
  native_decide

structure TightCouplingWindow where
  couplingWindow : ℕ
  errorWindow : ℕ
  tailSlack : ℕ
  couplingBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def TightCouplingWindow.errorControlled (w : TightCouplingWindow) : Prop :=
  w.errorWindow ≤ w.couplingWindow + w.tailSlack + w.slack

def tightCouplingWindowReady (w : TightCouplingWindow) : Prop :=
  0 < w.couplingWindow ∧ w.errorControlled ∧
    w.couplingBudget ≤ w.couplingWindow + w.errorWindow + w.slack

def TightCouplingWindow.certificate (w : TightCouplingWindow) : ℕ :=
  w.couplingWindow + w.errorWindow + w.tailSlack + w.couplingBudget + w.slack

theorem tightCoupling_couplingBudget_le_certificate (w : TightCouplingWindow) :
    w.couplingBudget ≤ w.certificate := by
  unfold TightCouplingWindow.certificate
  omega

def sampleTightCouplingWindow : TightCouplingWindow :=
  { couplingWindow := 5, errorWindow := 7, tailSlack := 2, couplingBudget := 14, slack := 2 }

example : tightCouplingWindowReady sampleTightCouplingWindow := by
  norm_num [tightCouplingWindowReady, TightCouplingWindow.errorControlled,
    sampleTightCouplingWindow]


structure TightCouplingSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def TightCouplingSchemasBudgetCertificate.controlled
    (c : TightCouplingSchemasBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def TightCouplingSchemasBudgetCertificate.budgetControlled
    (c : TightCouplingSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def TightCouplingSchemasBudgetCertificate.Ready
    (c : TightCouplingSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def TightCouplingSchemasBudgetCertificate.size
    (c : TightCouplingSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem tightCouplingSchemas_budgetCertificate_le_size
    (c : TightCouplingSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleTightCouplingSchemasBudgetCertificate :
    TightCouplingSchemasBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleTightCouplingSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [TightCouplingSchemasBudgetCertificate.controlled,
      sampleTightCouplingSchemasBudgetCertificate]
  · norm_num [TightCouplingSchemasBudgetCertificate.budgetControlled,
      sampleTightCouplingSchemasBudgetCertificate]

example : sampleTightCouplingSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [TightCouplingSchemasBudgetCertificate.controlled,
      sampleTightCouplingSchemasBudgetCertificate]
  · norm_num [TightCouplingSchemasBudgetCertificate.budgetControlled,
      sampleTightCouplingSchemasBudgetCertificate]

example :
    sampleTightCouplingSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleTightCouplingSchemasBudgetCertificate.size := by
  apply tightCouplingSchemas_budgetCertificate_le_size
  constructor
  · norm_num [TightCouplingSchemasBudgetCertificate.controlled,
      sampleTightCouplingSchemasBudgetCertificate]
  · norm_num [TightCouplingSchemasBudgetCertificate.budgetControlled,
      sampleTightCouplingSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_le_size :
    sampleTightCouplingSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleTightCouplingSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List TightCouplingSchemasBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleTightCouplingSchemasBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleTightCouplingSchemasBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppC.TightCouplingSchemas
