import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Theta saddle window schemas.

This module records finite bookkeeping for theta-type saddle windows.
-/

namespace AnalyticCombinatorics.PartB.Ch8.ThetaSaddleWindowSchemas

structure ThetaSaddleWindowData where
  thetaOrder : ℕ
  saddleScale : ℕ
  modularSlack : ℕ
deriving DecidableEq, Repr

def hasThetaOrder (d : ThetaSaddleWindowData) : Prop :=
  0 < d.thetaOrder

def saddleScaleControlled (d : ThetaSaddleWindowData) : Prop :=
  d.saddleScale ≤ d.thetaOrder + d.modularSlack

def thetaSaddleWindowReady (d : ThetaSaddleWindowData) : Prop :=
  hasThetaOrder d ∧ saddleScaleControlled d

def thetaSaddleWindowBudget (d : ThetaSaddleWindowData) : ℕ :=
  d.thetaOrder + d.saddleScale + d.modularSlack

theorem thetaSaddleWindowReady.hasThetaOrder {d : ThetaSaddleWindowData}
    (h : thetaSaddleWindowReady d) :
    hasThetaOrder d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem saddleScale_le_budget (d : ThetaSaddleWindowData) :
    d.saddleScale ≤ thetaSaddleWindowBudget d := by
  unfold thetaSaddleWindowBudget
  omega

def sampleThetaSaddleWindowData : ThetaSaddleWindowData :=
  { thetaOrder := 6, saddleScale := 8, modularSlack := 3 }

example : thetaSaddleWindowReady sampleThetaSaddleWindowData := by
  norm_num [thetaSaddleWindowReady, hasThetaOrder]
  norm_num [saddleScaleControlled, sampleThetaSaddleWindowData]

example : thetaSaddleWindowBudget sampleThetaSaddleWindowData = 17 := by
  native_decide

structure ThetaSaddleCertificateWindow where
  thetaOrder : ℕ
  saddleScale : ℕ
  modularSlack : ℕ
  thetaTransformBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def ThetaSaddleCertificateWindow.saddleControlled
    (w : ThetaSaddleCertificateWindow) : Prop :=
  w.saddleScale ≤ w.thetaOrder + w.modularSlack + w.slack

def ThetaSaddleCertificateWindow.transformControlled
    (w : ThetaSaddleCertificateWindow) : Prop :=
  w.thetaTransformBudget ≤ w.thetaOrder + w.saddleScale + w.modularSlack + w.slack

def thetaSaddleCertificateReady (w : ThetaSaddleCertificateWindow) : Prop :=
  0 < w.thetaOrder ∧
    w.saddleControlled ∧
    w.transformControlled

def ThetaSaddleCertificateWindow.certificate (w : ThetaSaddleCertificateWindow) : ℕ :=
  w.thetaOrder + w.saddleScale + w.modularSlack + w.slack

theorem thetaSaddle_transformBudget_le_certificate {w : ThetaSaddleCertificateWindow}
    (h : thetaSaddleCertificateReady w) :
    w.thetaTransformBudget ≤ w.certificate := by
  rcases h with ⟨_, _, htransform⟩
  exact htransform

def sampleThetaSaddleCertificateWindow : ThetaSaddleCertificateWindow :=
  { thetaOrder := 6, saddleScale := 8, modularSlack := 3, thetaTransformBudget := 16,
    slack := 0 }

example : thetaSaddleCertificateReady sampleThetaSaddleCertificateWindow := by
  norm_num [thetaSaddleCertificateReady, ThetaSaddleCertificateWindow.saddleControlled,
    ThetaSaddleCertificateWindow.transformControlled, sampleThetaSaddleCertificateWindow]

example : sampleThetaSaddleCertificateWindow.certificate = 17 := by
  native_decide


structure ThetaSaddleWindowSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def ThetaSaddleWindowSchemasBudgetCertificate.controlled
    (c : ThetaSaddleWindowSchemasBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def ThetaSaddleWindowSchemasBudgetCertificate.budgetControlled
    (c : ThetaSaddleWindowSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def ThetaSaddleWindowSchemasBudgetCertificate.Ready
    (c : ThetaSaddleWindowSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def ThetaSaddleWindowSchemasBudgetCertificate.size
    (c : ThetaSaddleWindowSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem thetaSaddleWindowSchemas_budgetCertificate_le_size
    (c : ThetaSaddleWindowSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleThetaSaddleWindowSchemasBudgetCertificate :
    ThetaSaddleWindowSchemasBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleThetaSaddleWindowSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [ThetaSaddleWindowSchemasBudgetCertificate.controlled,
      sampleThetaSaddleWindowSchemasBudgetCertificate]
  · norm_num [ThetaSaddleWindowSchemasBudgetCertificate.budgetControlled,
      sampleThetaSaddleWindowSchemasBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleThetaSaddleWindowSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleThetaSaddleWindowSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleThetaSaddleWindowSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [ThetaSaddleWindowSchemasBudgetCertificate.controlled,
      sampleThetaSaddleWindowSchemasBudgetCertificate]
  · norm_num [ThetaSaddleWindowSchemasBudgetCertificate.budgetControlled,
      sampleThetaSaddleWindowSchemasBudgetCertificate]

example :
    sampleThetaSaddleWindowSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleThetaSaddleWindowSchemasBudgetCertificate.size := by
  apply thetaSaddleWindowSchemas_budgetCertificate_le_size
  constructor
  · norm_num [ThetaSaddleWindowSchemasBudgetCertificate.controlled,
      sampleThetaSaddleWindowSchemasBudgetCertificate]
  · norm_num [ThetaSaddleWindowSchemasBudgetCertificate.budgetControlled,
      sampleThetaSaddleWindowSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List ThetaSaddleWindowSchemasBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleThetaSaddleWindowSchemasBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleThetaSaddleWindowSchemasBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch8.ThetaSaddleWindowSchemas
