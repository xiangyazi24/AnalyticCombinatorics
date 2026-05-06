import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Zeta residue window schemas.

This module records finite bookkeeping for zeta residue windows.
-/

namespace AnalyticCombinatorics.PartB.Ch5.ZetaResidueWindowSchemas

structure ZetaResidueWindowData where
  zetaOrder : ℕ
  residueWindow : ℕ
  zetaSlack : ℕ
deriving DecidableEq, Repr

def hasZetaOrder (d : ZetaResidueWindowData) : Prop :=
  0 < d.zetaOrder

def residueWindowControlled (d : ZetaResidueWindowData) : Prop :=
  d.residueWindow ≤ d.zetaOrder + d.zetaSlack

def zetaResidueReady (d : ZetaResidueWindowData) : Prop :=
  hasZetaOrder d ∧ residueWindowControlled d

def zetaResidueBudget (d : ZetaResidueWindowData) : ℕ :=
  d.zetaOrder + d.residueWindow + d.zetaSlack

theorem zetaResidueReady.hasZetaOrder {d : ZetaResidueWindowData}
    (h : zetaResidueReady d) :
    hasZetaOrder d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem residueWindow_le_budget (d : ZetaResidueWindowData) :
    d.residueWindow ≤ zetaResidueBudget d := by
  unfold zetaResidueBudget
  omega

def sampleZetaResidueWindowData : ZetaResidueWindowData :=
  { zetaOrder := 6, residueWindow := 8, zetaSlack := 3 }

example : zetaResidueReady sampleZetaResidueWindowData := by
  norm_num [zetaResidueReady, hasZetaOrder]
  norm_num [residueWindowControlled, sampleZetaResidueWindowData]

example : zetaResidueBudget sampleZetaResidueWindowData = 17 := by
  native_decide

structure ZetaResidueCertificateWindow where
  zetaOrder : ℕ
  residueWindow : ℕ
  zetaSlack : ℕ
  coefficientBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def ZetaResidueCertificateWindow.residueControlled
    (w : ZetaResidueCertificateWindow) : Prop :=
  w.residueWindow ≤ w.zetaOrder + w.zetaSlack + w.slack

def ZetaResidueCertificateWindow.coefficientControlled
    (w : ZetaResidueCertificateWindow) : Prop :=
  w.coefficientBudget ≤ w.zetaOrder + w.residueWindow + w.zetaSlack + w.slack

def zetaResidueCertificateReady (w : ZetaResidueCertificateWindow) : Prop :=
  0 < w.zetaOrder ∧
    w.residueControlled ∧
    w.coefficientControlled

def ZetaResidueCertificateWindow.certificate (w : ZetaResidueCertificateWindow) : ℕ :=
  w.zetaOrder + w.residueWindow + w.zetaSlack + w.slack

theorem zetaResidue_coefficientBudget_le_certificate {w : ZetaResidueCertificateWindow}
    (h : zetaResidueCertificateReady w) :
    w.coefficientBudget ≤ w.certificate := by
  rcases h with ⟨_, _, hcoeff⟩
  exact hcoeff

def sampleZetaResidueCertificateWindow : ZetaResidueCertificateWindow :=
  { zetaOrder := 6, residueWindow := 8, zetaSlack := 3, coefficientBudget := 16, slack := 0 }

example : zetaResidueCertificateReady sampleZetaResidueCertificateWindow := by
  norm_num [zetaResidueCertificateReady, ZetaResidueCertificateWindow.residueControlled,
    ZetaResidueCertificateWindow.coefficientControlled, sampleZetaResidueCertificateWindow]

example : sampleZetaResidueCertificateWindow.certificate = 17 := by
  native_decide


structure ZetaResidueWindowSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def ZetaResidueWindowSchemasBudgetCertificate.controlled
    (c : ZetaResidueWindowSchemasBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def ZetaResidueWindowSchemasBudgetCertificate.budgetControlled
    (c : ZetaResidueWindowSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def ZetaResidueWindowSchemasBudgetCertificate.Ready
    (c : ZetaResidueWindowSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def ZetaResidueWindowSchemasBudgetCertificate.size
    (c : ZetaResidueWindowSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem zetaResidueWindowSchemas_budgetCertificate_le_size
    (c : ZetaResidueWindowSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleZetaResidueWindowSchemasBudgetCertificate :
    ZetaResidueWindowSchemasBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleZetaResidueWindowSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [ZetaResidueWindowSchemasBudgetCertificate.controlled,
      sampleZetaResidueWindowSchemasBudgetCertificate]
  · norm_num [ZetaResidueWindowSchemasBudgetCertificate.budgetControlled,
      sampleZetaResidueWindowSchemasBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleZetaResidueWindowSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleZetaResidueWindowSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleZetaResidueWindowSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [ZetaResidueWindowSchemasBudgetCertificate.controlled,
      sampleZetaResidueWindowSchemasBudgetCertificate]
  · norm_num [ZetaResidueWindowSchemasBudgetCertificate.budgetControlled,
      sampleZetaResidueWindowSchemasBudgetCertificate]

example :
    sampleZetaResidueWindowSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleZetaResidueWindowSchemasBudgetCertificate.size := by
  apply zetaResidueWindowSchemas_budgetCertificate_le_size
  constructor
  · norm_num [ZetaResidueWindowSchemasBudgetCertificate.controlled,
      sampleZetaResidueWindowSchemasBudgetCertificate]
  · norm_num [ZetaResidueWindowSchemasBudgetCertificate.budgetControlled,
      sampleZetaResidueWindowSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List ZetaResidueWindowSchemasBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleZetaResidueWindowSchemasBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleZetaResidueWindowSchemasBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch5.ZetaResidueWindowSchemas
