import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Renewal-style Tauberian schemas.

This module records the finite positivity and span checks for renewal
sequences before analytic Tauberian conclusions are applied.
-/

namespace AnalyticCombinatorics.AppC.RenewalTauberianSchemas

structure RenewalData where
  span : ℕ
  meanNumerator : ℕ
  meanDenominator : ℕ
deriving DecidableEq, Repr

def renewalAperiodic (d : RenewalData) : Prop :=
  d.span = 1

def positiveMean (d : RenewalData) : Prop :=
  0 < d.meanNumerator ∧ 0 < d.meanDenominator

def renewalReady (d : RenewalData) : Prop :=
  renewalAperiodic d ∧ positiveMean d

def meanBudget (d : RenewalData) : ℕ :=
  d.meanNumerator + d.meanDenominator

theorem renewalReady.mean {d : RenewalData}
    (h : renewalReady d) :
    positiveMean d := by
  rcases h with ⟨hleft, hright⟩
  exact hright

theorem positiveMean_budget_pos {d : RenewalData}
    (h : positiveMean d) :
    0 < meanBudget d := by
  unfold positiveMean meanBudget at *
  omega

def sampleRenewal : RenewalData :=
  { span := 1, meanNumerator := 5, meanDenominator := 2 }

example : renewalReady sampleRenewal := by
  norm_num [renewalReady, renewalAperiodic, positiveMean, sampleRenewal]

example : meanBudget sampleRenewal = 7 := by
  native_decide

structure RenewalWindow where
  span : ℕ
  meanNumerator : ℕ
  meanDenominator : ℕ
  renewalBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def RenewalWindow.meanPositive (w : RenewalWindow) : Prop :=
  0 < w.meanNumerator ∧ 0 < w.meanDenominator

def RenewalWindow.renewalControlled (w : RenewalWindow) : Prop :=
  w.renewalBudget ≤ w.span + w.meanNumerator + w.meanDenominator + w.slack

def renewalWindowReady (w : RenewalWindow) : Prop :=
  w.span = 1 ∧
    w.meanPositive ∧
    w.renewalControlled

def RenewalWindow.certificate (w : RenewalWindow) : ℕ :=
  w.span + w.meanNumerator + w.meanDenominator + w.slack

theorem renewalBudget_le_certificate {w : RenewalWindow}
    (h : renewalWindowReady w) :
    w.renewalBudget ≤ w.certificate := by
  rcases h with ⟨_, _, hrenewal⟩
  exact hrenewal

def sampleRenewalWindow : RenewalWindow :=
  { span := 1, meanNumerator := 5, meanDenominator := 2, renewalBudget := 7, slack := 0 }

example : renewalWindowReady sampleRenewalWindow := by
  norm_num [renewalWindowReady, RenewalWindow.meanPositive, RenewalWindow.renewalControlled,
    sampleRenewalWindow]

example : sampleRenewalWindow.certificate = 8 := by
  native_decide


structure RenewalTauberianSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def RenewalTauberianSchemasBudgetCertificate.controlled
    (c : RenewalTauberianSchemasBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def RenewalTauberianSchemasBudgetCertificate.budgetControlled
    (c : RenewalTauberianSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def RenewalTauberianSchemasBudgetCertificate.Ready
    (c : RenewalTauberianSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def RenewalTauberianSchemasBudgetCertificate.size
    (c : RenewalTauberianSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem renewalTauberianSchemas_budgetCertificate_le_size
    (c : RenewalTauberianSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleRenewalTauberianSchemasBudgetCertificate :
    RenewalTauberianSchemasBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleRenewalTauberianSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [RenewalTauberianSchemasBudgetCertificate.controlled,
      sampleRenewalTauberianSchemasBudgetCertificate]
  · norm_num [RenewalTauberianSchemasBudgetCertificate.budgetControlled,
      sampleRenewalTauberianSchemasBudgetCertificate]

example : sampleRenewalTauberianSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [RenewalTauberianSchemasBudgetCertificate.controlled,
      sampleRenewalTauberianSchemasBudgetCertificate]
  · norm_num [RenewalTauberianSchemasBudgetCertificate.budgetControlled,
      sampleRenewalTauberianSchemasBudgetCertificate]

example :
    sampleRenewalTauberianSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleRenewalTauberianSchemasBudgetCertificate.size := by
  apply renewalTauberianSchemas_budgetCertificate_le_size
  constructor
  · norm_num [RenewalTauberianSchemasBudgetCertificate.controlled,
      sampleRenewalTauberianSchemasBudgetCertificate]
  · norm_num [RenewalTauberianSchemasBudgetCertificate.budgetControlled,
      sampleRenewalTauberianSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_le_size :
    sampleRenewalTauberianSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleRenewalTauberianSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List RenewalTauberianSchemasBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleRenewalTauberianSchemasBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleRenewalTauberianSchemasBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppC.RenewalTauberianSchemas
