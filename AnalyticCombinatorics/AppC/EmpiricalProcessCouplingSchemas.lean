import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Empirical process coupling schemas.

This module records finite bookkeeping for empirical process couplings.
-/

namespace AnalyticCombinatorics.AppC.EmpiricalProcessCouplingSchemas

structure EmpiricalProcessCouplingData where
  processScale : ℕ
  couplingError : ℕ
  envelopeSlack : ℕ
deriving DecidableEq, Repr

def hasProcessScale (d : EmpiricalProcessCouplingData) : Prop :=
  0 < d.processScale

def couplingErrorControlled (d : EmpiricalProcessCouplingData) : Prop :=
  d.couplingError ≤ d.processScale + d.envelopeSlack

def empiricalProcessCouplingReady
    (d : EmpiricalProcessCouplingData) : Prop :=
  hasProcessScale d ∧ couplingErrorControlled d

def empiricalProcessCouplingBudget
    (d : EmpiricalProcessCouplingData) : ℕ :=
  d.processScale + d.couplingError + d.envelopeSlack

theorem empiricalProcessCouplingReady.hasProcessScale
    {d : EmpiricalProcessCouplingData}
    (h : empiricalProcessCouplingReady d) :
    hasProcessScale d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem couplingError_le_budget (d : EmpiricalProcessCouplingData) :
    d.couplingError ≤ empiricalProcessCouplingBudget d := by
  unfold empiricalProcessCouplingBudget
  omega

def sampleEmpiricalProcessCouplingData : EmpiricalProcessCouplingData :=
  { processScale := 7, couplingError := 9, envelopeSlack := 3 }

example : empiricalProcessCouplingReady
    sampleEmpiricalProcessCouplingData := by
  norm_num [empiricalProcessCouplingReady, hasProcessScale]
  norm_num [couplingErrorControlled, sampleEmpiricalProcessCouplingData]

example :
    empiricalProcessCouplingBudget sampleEmpiricalProcessCouplingData = 19 := by
  native_decide

structure EmpiricalProcessCouplingWindow where
  processWindow : ℕ
  errorWindow : ℕ
  envelopeSlack : ℕ
  couplingBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def EmpiricalProcessCouplingWindow.errorControlled
    (w : EmpiricalProcessCouplingWindow) : Prop :=
  w.errorWindow ≤ w.processWindow + w.envelopeSlack + w.slack

def empiricalProcessCouplingWindowReady
    (w : EmpiricalProcessCouplingWindow) : Prop :=
  0 < w.processWindow ∧ w.errorControlled ∧
    w.couplingBudget ≤ w.processWindow + w.errorWindow + w.slack

def EmpiricalProcessCouplingWindow.certificate
    (w : EmpiricalProcessCouplingWindow) : ℕ :=
  w.processWindow + w.errorWindow + w.envelopeSlack + w.couplingBudget + w.slack

theorem empiricalProcessCoupling_couplingBudget_le_certificate
    (w : EmpiricalProcessCouplingWindow) :
    w.couplingBudget ≤ w.certificate := by
  unfold EmpiricalProcessCouplingWindow.certificate
  omega

def sampleEmpiricalProcessCouplingWindow : EmpiricalProcessCouplingWindow :=
  { processWindow := 6, errorWindow := 8, envelopeSlack := 2,
    couplingBudget := 15, slack := 1 }

example : empiricalProcessCouplingWindowReady
    sampleEmpiricalProcessCouplingWindow := by
  norm_num [empiricalProcessCouplingWindowReady,
    EmpiricalProcessCouplingWindow.errorControlled, sampleEmpiricalProcessCouplingWindow]


structure EmpiricalProcessCouplingSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def EmpiricalProcessCouplingSchemasBudgetCertificate.controlled
    (c : EmpiricalProcessCouplingSchemasBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def EmpiricalProcessCouplingSchemasBudgetCertificate.budgetControlled
    (c : EmpiricalProcessCouplingSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def EmpiricalProcessCouplingSchemasBudgetCertificate.Ready
    (c : EmpiricalProcessCouplingSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def EmpiricalProcessCouplingSchemasBudgetCertificate.size
    (c : EmpiricalProcessCouplingSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem empiricalProcessCouplingSchemas_budgetCertificate_le_size
    (c : EmpiricalProcessCouplingSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleEmpiricalProcessCouplingSchemasBudgetCertificate :
    EmpiricalProcessCouplingSchemasBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleEmpiricalProcessCouplingSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [EmpiricalProcessCouplingSchemasBudgetCertificate.controlled,
      sampleEmpiricalProcessCouplingSchemasBudgetCertificate]
  · norm_num [EmpiricalProcessCouplingSchemasBudgetCertificate.budgetControlled,
      sampleEmpiricalProcessCouplingSchemasBudgetCertificate]

example : sampleEmpiricalProcessCouplingSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [EmpiricalProcessCouplingSchemasBudgetCertificate.controlled,
      sampleEmpiricalProcessCouplingSchemasBudgetCertificate]
  · norm_num [EmpiricalProcessCouplingSchemasBudgetCertificate.budgetControlled,
      sampleEmpiricalProcessCouplingSchemasBudgetCertificate]

example :
    sampleEmpiricalProcessCouplingSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleEmpiricalProcessCouplingSchemasBudgetCertificate.size := by
  apply empiricalProcessCouplingSchemas_budgetCertificate_le_size
  constructor
  · norm_num [EmpiricalProcessCouplingSchemasBudgetCertificate.controlled,
      sampleEmpiricalProcessCouplingSchemasBudgetCertificate]
  · norm_num [EmpiricalProcessCouplingSchemasBudgetCertificate.budgetControlled,
      sampleEmpiricalProcessCouplingSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_le_size :
    sampleEmpiricalProcessCouplingSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleEmpiricalProcessCouplingSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady
    (data : List EmpiricalProcessCouplingSchemasBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleEmpiricalProcessCouplingSchemasBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleEmpiricalProcessCouplingSchemasBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppC.EmpiricalProcessCouplingSchemas
