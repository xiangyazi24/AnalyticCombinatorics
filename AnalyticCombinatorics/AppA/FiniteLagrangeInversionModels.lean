import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Finite Lagrange inversion models.

This module records finite bookkeeping for Lagrange inversion templates.
-/

namespace AnalyticCombinatorics.AppA.FiniteLagrangeInversionModels

structure LagrangeInversionData where
  inversionOrder : ℕ
  coefficientDepth : ℕ
  inversionSlack : ℕ
deriving DecidableEq, Repr

def hasInversionOrder (d : LagrangeInversionData) : Prop :=
  0 < d.inversionOrder

def coefficientDepthControlled (d : LagrangeInversionData) : Prop :=
  d.coefficientDepth ≤ d.inversionOrder + d.inversionSlack

def lagrangeInversionReady (d : LagrangeInversionData) : Prop :=
  hasInversionOrder d ∧ coefficientDepthControlled d

def lagrangeInversionBudget (d : LagrangeInversionData) : ℕ :=
  d.inversionOrder + d.coefficientDepth + d.inversionSlack

theorem lagrangeInversionReady.hasInversionOrder
    {d : LagrangeInversionData}
    (h : lagrangeInversionReady d) :
    hasInversionOrder d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem coefficientDepth_le_budget (d : LagrangeInversionData) :
    d.coefficientDepth ≤ lagrangeInversionBudget d := by
  unfold lagrangeInversionBudget
  omega

def sampleLagrangeInversionData : LagrangeInversionData :=
  { inversionOrder := 6, coefficientDepth := 8, inversionSlack := 3 }

example : lagrangeInversionReady sampleLagrangeInversionData := by
  norm_num [lagrangeInversionReady, hasInversionOrder]
  norm_num [coefficientDepthControlled, sampleLagrangeInversionData]

example : lagrangeInversionBudget sampleLagrangeInversionData = 17 := by
  native_decide

structure LagrangeInversionWindow where
  inversionOrder : ℕ
  coefficientDepth : ℕ
  inversionSlack : ℕ
  coefficientBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def LagrangeInversionWindow.depthControlled (w : LagrangeInversionWindow) : Prop :=
  w.coefficientDepth ≤ w.inversionOrder + w.inversionSlack + w.slack

def LagrangeInversionWindow.coefficientControlled (w : LagrangeInversionWindow) : Prop :=
  w.coefficientBudget ≤ w.inversionOrder + w.coefficientDepth + w.inversionSlack + w.slack

def lagrangeInversionWindowReady (w : LagrangeInversionWindow) : Prop :=
  0 < w.inversionOrder ∧
    w.depthControlled ∧
    w.coefficientControlled

def LagrangeInversionWindow.certificate (w : LagrangeInversionWindow) : ℕ :=
  w.inversionOrder + w.coefficientDepth + w.inversionSlack + w.slack

theorem lagrangeInversion_coefficientBudget_le_certificate {w : LagrangeInversionWindow}
    (h : lagrangeInversionWindowReady w) :
    w.coefficientBudget ≤ w.certificate := by
  rcases h with ⟨_, _, hcoeff⟩
  exact hcoeff

def sampleLagrangeInversionWindow : LagrangeInversionWindow :=
  { inversionOrder := 6, coefficientDepth := 8, inversionSlack := 3, coefficientBudget := 16,
    slack := 0 }

example : lagrangeInversionWindowReady sampleLagrangeInversionWindow := by
  norm_num [lagrangeInversionWindowReady, LagrangeInversionWindow.depthControlled,
    LagrangeInversionWindow.coefficientControlled, sampleLagrangeInversionWindow]

example : sampleLagrangeInversionWindow.certificate = 17 := by
  native_decide


structure FiniteLagrangeInversionModelsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def FiniteLagrangeInversionModelsBudgetCertificate.controlled
    (c : FiniteLagrangeInversionModelsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def FiniteLagrangeInversionModelsBudgetCertificate.budgetControlled
    (c : FiniteLagrangeInversionModelsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def FiniteLagrangeInversionModelsBudgetCertificate.Ready
    (c : FiniteLagrangeInversionModelsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def FiniteLagrangeInversionModelsBudgetCertificate.size
    (c : FiniteLagrangeInversionModelsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem finiteLagrangeInversionModels_budgetCertificate_le_size
    (c : FiniteLagrangeInversionModelsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleFiniteLagrangeInversionModelsBudgetCertificate :
    FiniteLagrangeInversionModelsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleFiniteLagrangeInversionModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [FiniteLagrangeInversionModelsBudgetCertificate.controlled,
      sampleFiniteLagrangeInversionModelsBudgetCertificate]
  · norm_num [FiniteLagrangeInversionModelsBudgetCertificate.budgetControlled,
      sampleFiniteLagrangeInversionModelsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleFiniteLagrangeInversionModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleFiniteLagrangeInversionModelsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleFiniteLagrangeInversionModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [FiniteLagrangeInversionModelsBudgetCertificate.controlled,
      sampleFiniteLagrangeInversionModelsBudgetCertificate]
  · norm_num [FiniteLagrangeInversionModelsBudgetCertificate.budgetControlled,
      sampleFiniteLagrangeInversionModelsBudgetCertificate]

example :
    sampleFiniteLagrangeInversionModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleFiniteLagrangeInversionModelsBudgetCertificate.size := by
  apply finiteLagrangeInversionModels_budgetCertificate_le_size
  constructor
  · norm_num [FiniteLagrangeInversionModelsBudgetCertificate.controlled,
      sampleFiniteLagrangeInversionModelsBudgetCertificate]
  · norm_num [FiniteLagrangeInversionModelsBudgetCertificate.budgetControlled,
      sampleFiniteLagrangeInversionModelsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady
    (data : List FiniteLagrangeInversionModelsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleFiniteLagrangeInversionModelsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleFiniteLagrangeInversionModelsBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppA.FiniteLagrangeInversionModels
