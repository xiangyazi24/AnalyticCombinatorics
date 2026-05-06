import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Smooth implicit transfer window schemas.

This module records finite bookkeeping for smooth implicit transfer windows.
-/

namespace AnalyticCombinatorics.PartB.Ch7.SmoothImplicitTransferWindowSchemas

structure SmoothImplicitTransferData where
  smoothOrder : ℕ
  transferWindow : ℕ
  implicitSlack : ℕ
deriving DecidableEq, Repr

def hasSmoothOrder (d : SmoothImplicitTransferData) : Prop :=
  0 < d.smoothOrder

def transferWindowControlled (d : SmoothImplicitTransferData) : Prop :=
  d.transferWindow ≤ d.smoothOrder + d.implicitSlack

def smoothImplicitTransferReady (d : SmoothImplicitTransferData) : Prop :=
  hasSmoothOrder d ∧ transferWindowControlled d

def smoothImplicitTransferBudget (d : SmoothImplicitTransferData) : ℕ :=
  d.smoothOrder + d.transferWindow + d.implicitSlack

theorem smoothImplicitTransferReady.hasSmoothOrder
    {d : SmoothImplicitTransferData}
    (h : smoothImplicitTransferReady d) :
    hasSmoothOrder d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem transferWindow_le_budget (d : SmoothImplicitTransferData) :
    d.transferWindow ≤ smoothImplicitTransferBudget d := by
  unfold smoothImplicitTransferBudget
  omega

def sampleSmoothImplicitTransferData : SmoothImplicitTransferData :=
  { smoothOrder := 6, transferWindow := 8, implicitSlack := 3 }

example : smoothImplicitTransferReady sampleSmoothImplicitTransferData := by
  norm_num [smoothImplicitTransferReady, hasSmoothOrder]
  norm_num [transferWindowControlled, sampleSmoothImplicitTransferData]

example : smoothImplicitTransferBudget sampleSmoothImplicitTransferData = 17 := by
  native_decide

/-- Finite executable readiness audit for smooth implicit transfer windows. -/
def smoothImplicitTransferListReady
    (windows : List SmoothImplicitTransferData) : Bool :=
  windows.all fun d =>
    0 < d.smoothOrder && d.transferWindow ≤ d.smoothOrder + d.implicitSlack

theorem smoothImplicitTransferList_readyWindow :
    smoothImplicitTransferListReady
      [{ smoothOrder := 4, transferWindow := 5, implicitSlack := 1 },
       { smoothOrder := 6, transferWindow := 8, implicitSlack := 3 }] = true := by
  unfold smoothImplicitTransferListReady
  native_decide

structure SmoothImplicitTransferBudgetCertificate where
  smoothOrderWindow : ℕ
  transferWindow : ℕ
  implicitSlackWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def SmoothImplicitTransferBudgetCertificate.controlled
    (c : SmoothImplicitTransferBudgetCertificate) : Prop :=
  0 < c.smoothOrderWindow ∧
    c.transferWindow ≤ c.smoothOrderWindow + c.implicitSlackWindow + c.slack

def SmoothImplicitTransferBudgetCertificate.budgetControlled
    (c : SmoothImplicitTransferBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.smoothOrderWindow + c.transferWindow + c.implicitSlackWindow + c.slack

def SmoothImplicitTransferBudgetCertificate.Ready
    (c : SmoothImplicitTransferBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def SmoothImplicitTransferBudgetCertificate.size
    (c : SmoothImplicitTransferBudgetCertificate) : ℕ :=
  c.smoothOrderWindow + c.transferWindow + c.implicitSlackWindow + c.slack

theorem smoothImplicitTransfer_budgetCertificate_le_size
    (c : SmoothImplicitTransferBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleSmoothImplicitTransferBudgetCertificate :
    SmoothImplicitTransferBudgetCertificate :=
  { smoothOrderWindow := 6
    transferWindow := 8
    implicitSlackWindow := 3
    certificateBudgetWindow := 18
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleSmoothImplicitTransferBudgetCertificate.Ready := by
  constructor
  · norm_num [SmoothImplicitTransferBudgetCertificate.controlled,
      sampleSmoothImplicitTransferBudgetCertificate]
  · norm_num [SmoothImplicitTransferBudgetCertificate.budgetControlled,
      sampleSmoothImplicitTransferBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleSmoothImplicitTransferBudgetCertificate.certificateBudgetWindow ≤
      sampleSmoothImplicitTransferBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleSmoothImplicitTransferBudgetCertificate.Ready := by
  constructor
  · norm_num [SmoothImplicitTransferBudgetCertificate.controlled,
      sampleSmoothImplicitTransferBudgetCertificate]
  · norm_num [SmoothImplicitTransferBudgetCertificate.budgetControlled,
      sampleSmoothImplicitTransferBudgetCertificate]

example :
    sampleSmoothImplicitTransferBudgetCertificate.certificateBudgetWindow ≤
      sampleSmoothImplicitTransferBudgetCertificate.size := by
  apply smoothImplicitTransfer_budgetCertificate_le_size
  constructor
  · norm_num [SmoothImplicitTransferBudgetCertificate.controlled,
      sampleSmoothImplicitTransferBudgetCertificate]
  · norm_num [SmoothImplicitTransferBudgetCertificate.budgetControlled,
      sampleSmoothImplicitTransferBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady
    (data : List SmoothImplicitTransferBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleSmoothImplicitTransferBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleSmoothImplicitTransferBudgetCertificate
  native_decide
end AnalyticCombinatorics.PartB.Ch7.SmoothImplicitTransferWindowSchemas
