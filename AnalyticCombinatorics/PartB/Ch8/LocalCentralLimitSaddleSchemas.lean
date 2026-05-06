import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Local central limit saddle schemas.

This module records finite bookkeeping for saddle local central limits.
-/

namespace AnalyticCombinatorics.PartB.Ch8.LocalCentralLimitSaddleSchemas

structure LocalCentralLimitSaddleData where
  saddleVariance : ℕ
  latticeWindow : ℕ
  gaussianSlack : ℕ
deriving DecidableEq, Repr

def hasSaddleVariance (d : LocalCentralLimitSaddleData) : Prop :=
  0 < d.saddleVariance

def latticeWindowControlled (d : LocalCentralLimitSaddleData) : Prop :=
  d.latticeWindow ≤ d.saddleVariance + d.gaussianSlack

def localCentralLimitSaddleReady
    (d : LocalCentralLimitSaddleData) : Prop :=
  hasSaddleVariance d ∧ latticeWindowControlled d

def localCentralLimitSaddleBudget
    (d : LocalCentralLimitSaddleData) : ℕ :=
  d.saddleVariance + d.latticeWindow + d.gaussianSlack

theorem localCentralLimitSaddleReady.hasSaddleVariance
    {d : LocalCentralLimitSaddleData}
    (h : localCentralLimitSaddleReady d) :
    hasSaddleVariance d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem latticeWindow_le_budget (d : LocalCentralLimitSaddleData) :
    d.latticeWindow ≤ localCentralLimitSaddleBudget d := by
  unfold localCentralLimitSaddleBudget
  omega

def sampleLocalCentralLimitSaddleData : LocalCentralLimitSaddleData :=
  { saddleVariance := 6, latticeWindow := 8, gaussianSlack := 3 }

example : localCentralLimitSaddleReady
    sampleLocalCentralLimitSaddleData := by
  norm_num [localCentralLimitSaddleReady, hasSaddleVariance]
  norm_num [latticeWindowControlled, sampleLocalCentralLimitSaddleData]

example :
    localCentralLimitSaddleBudget sampleLocalCentralLimitSaddleData = 17 := by
  native_decide


structure LocalCentralLimitSaddleSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def LocalCentralLimitSaddleSchemasBudgetCertificate.controlled
    (c : LocalCentralLimitSaddleSchemasBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def LocalCentralLimitSaddleSchemasBudgetCertificate.budgetControlled
    (c : LocalCentralLimitSaddleSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def LocalCentralLimitSaddleSchemasBudgetCertificate.Ready
    (c : LocalCentralLimitSaddleSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def LocalCentralLimitSaddleSchemasBudgetCertificate.size
    (c : LocalCentralLimitSaddleSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem localCentralLimitSaddleSchemas_budgetCertificate_le_size
    (c : LocalCentralLimitSaddleSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleLocalCentralLimitSaddleSchemasBudgetCertificate :
    LocalCentralLimitSaddleSchemasBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleLocalCentralLimitSaddleSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [LocalCentralLimitSaddleSchemasBudgetCertificate.controlled,
      sampleLocalCentralLimitSaddleSchemasBudgetCertificate]
  · norm_num [LocalCentralLimitSaddleSchemasBudgetCertificate.budgetControlled,
      sampleLocalCentralLimitSaddleSchemasBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleLocalCentralLimitSaddleSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleLocalCentralLimitSaddleSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleLocalCentralLimitSaddleSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [LocalCentralLimitSaddleSchemasBudgetCertificate.controlled,
      sampleLocalCentralLimitSaddleSchemasBudgetCertificate]
  · norm_num [LocalCentralLimitSaddleSchemasBudgetCertificate.budgetControlled,
      sampleLocalCentralLimitSaddleSchemasBudgetCertificate]

example :
    sampleLocalCentralLimitSaddleSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleLocalCentralLimitSaddleSchemasBudgetCertificate.size := by
  apply localCentralLimitSaddleSchemas_budgetCertificate_le_size
  constructor
  · norm_num [LocalCentralLimitSaddleSchemasBudgetCertificate.controlled,
      sampleLocalCentralLimitSaddleSchemasBudgetCertificate]
  · norm_num [LocalCentralLimitSaddleSchemasBudgetCertificate.budgetControlled,
      sampleLocalCentralLimitSaddleSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady
    (data : List LocalCentralLimitSaddleSchemasBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleLocalCentralLimitSaddleSchemasBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleLocalCentralLimitSaddleSchemasBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch8.LocalCentralLimitSaddleSchemas

