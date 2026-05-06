import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Lagrange inversion window schemas.

This module records finite bookkeeping for Lagrange inversion windows.
-/

namespace AnalyticCombinatorics.PartB.Ch7.LagrangeInversionWindowSchemas

structure LagrangeWindowData where
  inversionDepth : ℕ
  singularWindow : ℕ
  transferSlack : ℕ
deriving DecidableEq, Repr

def hasInversionDepth (d : LagrangeWindowData) : Prop :=
  0 < d.inversionDepth

def singularWindowControlled (d : LagrangeWindowData) : Prop :=
  d.singularWindow ≤ d.inversionDepth + d.transferSlack

def lagrangeWindowReady (d : LagrangeWindowData) : Prop :=
  hasInversionDepth d ∧ singularWindowControlled d

def lagrangeWindowBudget (d : LagrangeWindowData) : ℕ :=
  d.inversionDepth + d.singularWindow + d.transferSlack

theorem lagrangeWindowReady.hasInversionDepth {d : LagrangeWindowData}
    (h : lagrangeWindowReady d) :
    hasInversionDepth d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem singularWindow_le_budget (d : LagrangeWindowData) :
    d.singularWindow ≤ lagrangeWindowBudget d := by
  unfold lagrangeWindowBudget
  omega

def sampleLagrangeWindowData : LagrangeWindowData :=
  { inversionDepth := 6, singularWindow := 8, transferSlack := 3 }

example : lagrangeWindowReady sampleLagrangeWindowData := by
  norm_num [lagrangeWindowReady, hasInversionDepth]
  norm_num [singularWindowControlled, sampleLagrangeWindowData]

example : lagrangeWindowBudget sampleLagrangeWindowData = 17 := by
  native_decide

structure LagrangeCertificateWindow where
  inversionDepth : ℕ
  singularWindow : ℕ
  transferSlack : ℕ
  coefficientBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def LagrangeCertificateWindow.singularControlled (w : LagrangeCertificateWindow) : Prop :=
  w.singularWindow ≤ w.inversionDepth + w.transferSlack + w.slack

def LagrangeCertificateWindow.coefficientControlled (w : LagrangeCertificateWindow) : Prop :=
  w.coefficientBudget ≤ w.inversionDepth + w.singularWindow + w.transferSlack + w.slack

def lagrangeCertificateReady (w : LagrangeCertificateWindow) : Prop :=
  0 < w.inversionDepth ∧
    w.singularControlled ∧
    w.coefficientControlled

def LagrangeCertificateWindow.certificate (w : LagrangeCertificateWindow) : ℕ :=
  w.inversionDepth + w.singularWindow + w.transferSlack + w.slack

theorem lagrange_coefficientBudget_le_certificate {w : LagrangeCertificateWindow}
    (h : lagrangeCertificateReady w) :
    w.coefficientBudget ≤ w.certificate := by
  rcases h with ⟨_, _, hcoeff⟩
  exact hcoeff

def sampleLagrangeCertificateWindow : LagrangeCertificateWindow :=
  { inversionDepth := 6, singularWindow := 8, transferSlack := 3, coefficientBudget := 16,
    slack := 0 }

example : lagrangeCertificateReady sampleLagrangeCertificateWindow := by
  norm_num [lagrangeCertificateReady, LagrangeCertificateWindow.singularControlled,
    LagrangeCertificateWindow.coefficientControlled, sampleLagrangeCertificateWindow]

example : sampleLagrangeCertificateWindow.certificate = 17 := by
  native_decide


structure LagrangeInversionWindowSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def LagrangeInversionWindowSchemasBudgetCertificate.controlled
    (c : LagrangeInversionWindowSchemasBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def LagrangeInversionWindowSchemasBudgetCertificate.budgetControlled
    (c : LagrangeInversionWindowSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def LagrangeInversionWindowSchemasBudgetCertificate.Ready
    (c : LagrangeInversionWindowSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def LagrangeInversionWindowSchemasBudgetCertificate.size
    (c : LagrangeInversionWindowSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem lagrangeInversionWindowSchemas_budgetCertificate_le_size
    (c : LagrangeInversionWindowSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleLagrangeInversionWindowSchemasBudgetCertificate :
    LagrangeInversionWindowSchemasBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleLagrangeInversionWindowSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [LagrangeInversionWindowSchemasBudgetCertificate.controlled,
      sampleLagrangeInversionWindowSchemasBudgetCertificate]
  · norm_num [LagrangeInversionWindowSchemasBudgetCertificate.budgetControlled,
      sampleLagrangeInversionWindowSchemasBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleLagrangeInversionWindowSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleLagrangeInversionWindowSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleLagrangeInversionWindowSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [LagrangeInversionWindowSchemasBudgetCertificate.controlled,
      sampleLagrangeInversionWindowSchemasBudgetCertificate]
  · norm_num [LagrangeInversionWindowSchemasBudgetCertificate.budgetControlled,
      sampleLagrangeInversionWindowSchemasBudgetCertificate]

example :
    sampleLagrangeInversionWindowSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleLagrangeInversionWindowSchemasBudgetCertificate.size := by
  apply lagrangeInversionWindowSchemas_budgetCertificate_le_size
  constructor
  · norm_num [LagrangeInversionWindowSchemasBudgetCertificate.controlled,
      sampleLagrangeInversionWindowSchemasBudgetCertificate]
  · norm_num [LagrangeInversionWindowSchemasBudgetCertificate.budgetControlled,
      sampleLagrangeInversionWindowSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady
    (data : List LagrangeInversionWindowSchemasBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleLagrangeInversionWindowSchemasBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleLagrangeInversionWindowSchemasBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch7.LagrangeInversionWindowSchemas
