import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Algebraic Puiseux window schemas.

This module records finite bookkeeping for Puiseux expansion windows.
-/

namespace AnalyticCombinatorics.PartB.Ch6.AlgebraicPuiseuxWindowSchemas

structure AlgebraicPuiseuxWindowData where
  puiseuxOrder : ℕ
  branchWindow : ℕ
  algebraicSlack : ℕ
deriving DecidableEq, Repr

def hasPuiseuxOrder (d : AlgebraicPuiseuxWindowData) : Prop :=
  0 < d.puiseuxOrder

def branchWindowControlled (d : AlgebraicPuiseuxWindowData) : Prop :=
  d.branchWindow ≤ d.puiseuxOrder + d.algebraicSlack

def algebraicPuiseuxWindowReady
    (d : AlgebraicPuiseuxWindowData) : Prop :=
  hasPuiseuxOrder d ∧ branchWindowControlled d

def algebraicPuiseuxWindowBudget
    (d : AlgebraicPuiseuxWindowData) : ℕ :=
  d.puiseuxOrder + d.branchWindow + d.algebraicSlack

theorem algebraicPuiseuxWindowReady.hasPuiseuxOrder
    {d : AlgebraicPuiseuxWindowData}
    (h : algebraicPuiseuxWindowReady d) :
    hasPuiseuxOrder d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem branchWindow_le_budget (d : AlgebraicPuiseuxWindowData) :
    d.branchWindow ≤ algebraicPuiseuxWindowBudget d := by
  unfold algebraicPuiseuxWindowBudget
  omega

def sampleAlgebraicPuiseuxWindowData : AlgebraicPuiseuxWindowData :=
  { puiseuxOrder := 6, branchWindow := 8, algebraicSlack := 3 }

example : algebraicPuiseuxWindowReady
    sampleAlgebraicPuiseuxWindowData := by
  norm_num [algebraicPuiseuxWindowReady, hasPuiseuxOrder]
  norm_num [branchWindowControlled, sampleAlgebraicPuiseuxWindowData]

example :
    algebraicPuiseuxWindowBudget sampleAlgebraicPuiseuxWindowData = 17 := by
  native_decide


structure AlgebraicPuiseuxWindowSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def AlgebraicPuiseuxWindowSchemasBudgetCertificate.controlled
    (c : AlgebraicPuiseuxWindowSchemasBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def AlgebraicPuiseuxWindowSchemasBudgetCertificate.budgetControlled
    (c : AlgebraicPuiseuxWindowSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def AlgebraicPuiseuxWindowSchemasBudgetCertificate.Ready
    (c : AlgebraicPuiseuxWindowSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def AlgebraicPuiseuxWindowSchemasBudgetCertificate.size
    (c : AlgebraicPuiseuxWindowSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem algebraicPuiseuxWindowSchemas_budgetCertificate_le_size
    (c : AlgebraicPuiseuxWindowSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleAlgebraicPuiseuxWindowSchemasBudgetCertificate :
    AlgebraicPuiseuxWindowSchemasBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleAlgebraicPuiseuxWindowSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [AlgebraicPuiseuxWindowSchemasBudgetCertificate.controlled,
      sampleAlgebraicPuiseuxWindowSchemasBudgetCertificate]
  · norm_num [AlgebraicPuiseuxWindowSchemasBudgetCertificate.budgetControlled,
      sampleAlgebraicPuiseuxWindowSchemasBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleAlgebraicPuiseuxWindowSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleAlgebraicPuiseuxWindowSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleAlgebraicPuiseuxWindowSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [AlgebraicPuiseuxWindowSchemasBudgetCertificate.controlled,
      sampleAlgebraicPuiseuxWindowSchemasBudgetCertificate]
  · norm_num [AlgebraicPuiseuxWindowSchemasBudgetCertificate.budgetControlled,
      sampleAlgebraicPuiseuxWindowSchemasBudgetCertificate]

example :
    sampleAlgebraicPuiseuxWindowSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleAlgebraicPuiseuxWindowSchemasBudgetCertificate.size := by
  apply algebraicPuiseuxWindowSchemas_budgetCertificate_le_size
  constructor
  · norm_num [AlgebraicPuiseuxWindowSchemasBudgetCertificate.controlled,
      sampleAlgebraicPuiseuxWindowSchemasBudgetCertificate]
  · norm_num [AlgebraicPuiseuxWindowSchemasBudgetCertificate.budgetControlled,
      sampleAlgebraicPuiseuxWindowSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady
    (data : List AlgebraicPuiseuxWindowSchemasBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleAlgebraicPuiseuxWindowSchemasBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleAlgebraicPuiseuxWindowSchemasBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch6.AlgebraicPuiseuxWindowSchemas
