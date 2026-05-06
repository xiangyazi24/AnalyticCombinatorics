import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Stein coupling window schemas.

This module records finite bookkeeping for Stein coupling windows.
-/

namespace AnalyticCombinatorics.AppC.SteinCouplingWindowSchemas

structure SteinCouplingWindowData where
  steinScale : ℕ
  couplingError : ℕ
  approximationSlack : ℕ
deriving DecidableEq, Repr

def hasSteinScale (d : SteinCouplingWindowData) : Prop :=
  0 < d.steinScale

def couplingErrorControlled (d : SteinCouplingWindowData) : Prop :=
  d.couplingError ≤ d.steinScale + d.approximationSlack

def steinCouplingWindowReady (d : SteinCouplingWindowData) : Prop :=
  hasSteinScale d ∧ couplingErrorControlled d

def steinCouplingWindowBudget (d : SteinCouplingWindowData) : ℕ :=
  d.steinScale + d.couplingError + d.approximationSlack

theorem steinCouplingWindowReady.hasSteinScale
    {d : SteinCouplingWindowData}
    (h : steinCouplingWindowReady d) :
    hasSteinScale d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem couplingError_le_budget (d : SteinCouplingWindowData) :
    d.couplingError ≤ steinCouplingWindowBudget d := by
  unfold steinCouplingWindowBudget
  omega

def sampleSteinCouplingWindowData : SteinCouplingWindowData :=
  { steinScale := 6, couplingError := 8, approximationSlack := 3 }

example : steinCouplingWindowReady sampleSteinCouplingWindowData := by
  norm_num [steinCouplingWindowReady, hasSteinScale]
  norm_num [couplingErrorControlled, sampleSteinCouplingWindowData]

example : steinCouplingWindowBudget sampleSteinCouplingWindowData = 17 := by
  native_decide

structure SteinCouplingCertificateWindow where
  steinWindow : ℕ
  errorWindow : ℕ
  approximationSlack : ℕ
  steinBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def SteinCouplingCertificateWindow.errorControlled
    (w : SteinCouplingCertificateWindow) : Prop :=
  w.errorWindow ≤ w.steinWindow + w.approximationSlack + w.slack

def steinCouplingCertificateReady (w : SteinCouplingCertificateWindow) : Prop :=
  0 < w.steinWindow ∧ w.errorControlled ∧
    w.steinBudget ≤ w.steinWindow + w.errorWindow + w.slack

def SteinCouplingCertificateWindow.certificate
    (w : SteinCouplingCertificateWindow) : ℕ :=
  w.steinWindow + w.errorWindow + w.approximationSlack + w.steinBudget + w.slack

theorem steinCoupling_steinBudget_le_certificate
    (w : SteinCouplingCertificateWindow) :
    w.steinBudget ≤ w.certificate := by
  unfold SteinCouplingCertificateWindow.certificate
  omega

def sampleSteinCouplingCertificateWindow : SteinCouplingCertificateWindow :=
  { steinWindow := 5, errorWindow := 7, approximationSlack := 2, steinBudget := 14, slack := 2 }

example : steinCouplingCertificateReady sampleSteinCouplingCertificateWindow := by
  norm_num [steinCouplingCertificateReady,
    SteinCouplingCertificateWindow.errorControlled, sampleSteinCouplingCertificateWindow]


structure SteinCouplingWindowSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def SteinCouplingWindowSchemasBudgetCertificate.controlled
    (c : SteinCouplingWindowSchemasBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def SteinCouplingWindowSchemasBudgetCertificate.budgetControlled
    (c : SteinCouplingWindowSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def SteinCouplingWindowSchemasBudgetCertificate.Ready
    (c : SteinCouplingWindowSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def SteinCouplingWindowSchemasBudgetCertificate.size
    (c : SteinCouplingWindowSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem steinCouplingWindowSchemas_budgetCertificate_le_size
    (c : SteinCouplingWindowSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleSteinCouplingWindowSchemasBudgetCertificate :
    SteinCouplingWindowSchemasBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleSteinCouplingWindowSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [SteinCouplingWindowSchemasBudgetCertificate.controlled,
      sampleSteinCouplingWindowSchemasBudgetCertificate]
  · norm_num [SteinCouplingWindowSchemasBudgetCertificate.budgetControlled,
      sampleSteinCouplingWindowSchemasBudgetCertificate]

example : sampleSteinCouplingWindowSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [SteinCouplingWindowSchemasBudgetCertificate.controlled,
      sampleSteinCouplingWindowSchemasBudgetCertificate]
  · norm_num [SteinCouplingWindowSchemasBudgetCertificate.budgetControlled,
      sampleSteinCouplingWindowSchemasBudgetCertificate]

example :
    sampleSteinCouplingWindowSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleSteinCouplingWindowSchemasBudgetCertificate.size := by
  apply steinCouplingWindowSchemas_budgetCertificate_le_size
  constructor
  · norm_num [SteinCouplingWindowSchemasBudgetCertificate.controlled,
      sampleSteinCouplingWindowSchemasBudgetCertificate]
  · norm_num [SteinCouplingWindowSchemasBudgetCertificate.budgetControlled,
      sampleSteinCouplingWindowSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_le_size :
    sampleSteinCouplingWindowSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleSteinCouplingWindowSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List SteinCouplingWindowSchemasBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleSteinCouplingWindowSchemasBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleSteinCouplingWindowSchemasBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppC.SteinCouplingWindowSchemas
