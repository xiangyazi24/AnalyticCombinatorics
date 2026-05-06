import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Puiseux transfer remainder schemas.

This module records finite bookkeeping for Puiseux transfer remainders.
-/

namespace AnalyticCombinatorics.PartB.Ch6.PuiseuxTransferRemainderSchemas

structure PuiseuxTransferRemainderData where
  puiseuxOrder : ℕ
  remainderDepth : ℕ
  transferSlack : ℕ
deriving DecidableEq, Repr

def hasPuiseuxOrder (d : PuiseuxTransferRemainderData) : Prop :=
  0 < d.puiseuxOrder

def remainderDepthControlled (d : PuiseuxTransferRemainderData) : Prop :=
  d.remainderDepth ≤ d.puiseuxOrder + d.transferSlack

def puiseuxTransferRemainderReady
    (d : PuiseuxTransferRemainderData) : Prop :=
  hasPuiseuxOrder d ∧ remainderDepthControlled d

def puiseuxTransferRemainderBudget
    (d : PuiseuxTransferRemainderData) : ℕ :=
  d.puiseuxOrder + d.remainderDepth + d.transferSlack

theorem puiseuxTransferRemainderReady.hasPuiseuxOrder
    {d : PuiseuxTransferRemainderData}
    (h : puiseuxTransferRemainderReady d) :
    hasPuiseuxOrder d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem remainderDepth_le_budget (d : PuiseuxTransferRemainderData) :
    d.remainderDepth ≤ puiseuxTransferRemainderBudget d := by
  unfold puiseuxTransferRemainderBudget
  omega

def samplePuiseuxTransferRemainderData : PuiseuxTransferRemainderData :=
  { puiseuxOrder := 6, remainderDepth := 8, transferSlack := 3 }

example : puiseuxTransferRemainderReady
    samplePuiseuxTransferRemainderData := by
  norm_num [puiseuxTransferRemainderReady, hasPuiseuxOrder]
  norm_num [remainderDepthControlled, samplePuiseuxTransferRemainderData]

example :
    puiseuxTransferRemainderBudget samplePuiseuxTransferRemainderData = 17 := by
  native_decide


structure PuiseuxTransferRemainderSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def PuiseuxTransferRemainderSchemasBudgetCertificate.controlled
    (c : PuiseuxTransferRemainderSchemasBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def PuiseuxTransferRemainderSchemasBudgetCertificate.budgetControlled
    (c : PuiseuxTransferRemainderSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def PuiseuxTransferRemainderSchemasBudgetCertificate.Ready
    (c : PuiseuxTransferRemainderSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def PuiseuxTransferRemainderSchemasBudgetCertificate.size
    (c : PuiseuxTransferRemainderSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem puiseuxTransferRemainderSchemas_budgetCertificate_le_size
    (c : PuiseuxTransferRemainderSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def samplePuiseuxTransferRemainderSchemasBudgetCertificate :
    PuiseuxTransferRemainderSchemasBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    samplePuiseuxTransferRemainderSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [PuiseuxTransferRemainderSchemasBudgetCertificate.controlled,
      samplePuiseuxTransferRemainderSchemasBudgetCertificate]
  · norm_num [PuiseuxTransferRemainderSchemasBudgetCertificate.budgetControlled,
      samplePuiseuxTransferRemainderSchemasBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    samplePuiseuxTransferRemainderSchemasBudgetCertificate.certificateBudgetWindow ≤
      samplePuiseuxTransferRemainderSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : samplePuiseuxTransferRemainderSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [PuiseuxTransferRemainderSchemasBudgetCertificate.controlled,
      samplePuiseuxTransferRemainderSchemasBudgetCertificate]
  · norm_num [PuiseuxTransferRemainderSchemasBudgetCertificate.budgetControlled,
      samplePuiseuxTransferRemainderSchemasBudgetCertificate]

example :
    samplePuiseuxTransferRemainderSchemasBudgetCertificate.certificateBudgetWindow ≤
      samplePuiseuxTransferRemainderSchemasBudgetCertificate.size := by
  apply puiseuxTransferRemainderSchemas_budgetCertificate_le_size
  constructor
  · norm_num [PuiseuxTransferRemainderSchemasBudgetCertificate.controlled,
      samplePuiseuxTransferRemainderSchemasBudgetCertificate]
  · norm_num [PuiseuxTransferRemainderSchemasBudgetCertificate.budgetControlled,
      samplePuiseuxTransferRemainderSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady
    (data : List PuiseuxTransferRemainderSchemasBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [samplePuiseuxTransferRemainderSchemasBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady samplePuiseuxTransferRemainderSchemasBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch6.PuiseuxTransferRemainderSchemas
