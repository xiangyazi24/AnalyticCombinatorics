import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Bounded Lipschitz coupling window schemas.

This module records finite bookkeeping for bounded Lipschitz couplings.
-/

namespace AnalyticCombinatorics.AppC.BoundedLipschitzCouplingWindowSchemas

structure BoundedLipschitzCouplingWindowData where
  couplingTests : ℕ
  lipschitzWindow : ℕ
  couplingSlack : ℕ
deriving DecidableEq, Repr

def hasCouplingTests
    (d : BoundedLipschitzCouplingWindowData) : Prop :=
  0 < d.couplingTests

def lipschitzWindowControlled
    (d : BoundedLipschitzCouplingWindowData) : Prop :=
  d.lipschitzWindow ≤ d.couplingTests + d.couplingSlack

def boundedLipschitzCouplingReady
    (d : BoundedLipschitzCouplingWindowData) : Prop :=
  hasCouplingTests d ∧ lipschitzWindowControlled d

def boundedLipschitzCouplingBudget
    (d : BoundedLipschitzCouplingWindowData) : ℕ :=
  d.couplingTests + d.lipschitzWindow + d.couplingSlack

theorem boundedLipschitzCouplingReady.hasCouplingTests
    {d : BoundedLipschitzCouplingWindowData}
    (h : boundedLipschitzCouplingReady d) :
    hasCouplingTests d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem lipschitzWindow_le_budget
    (d : BoundedLipschitzCouplingWindowData) :
    d.lipschitzWindow ≤ boundedLipschitzCouplingBudget d := by
  unfold boundedLipschitzCouplingBudget
  omega

def sampleBoundedLipschitzCouplingWindowData :
    BoundedLipschitzCouplingWindowData :=
  { couplingTests := 6, lipschitzWindow := 8, couplingSlack := 3 }

example : boundedLipschitzCouplingReady
    sampleBoundedLipschitzCouplingWindowData := by
  norm_num [boundedLipschitzCouplingReady, hasCouplingTests]
  norm_num [lipschitzWindowControlled, sampleBoundedLipschitzCouplingWindowData]

example :
    boundedLipschitzCouplingBudget sampleBoundedLipschitzCouplingWindowData = 17 := by
  native_decide

structure BoundedLipschitzCouplingCertificateWindow where
  testWindow : ℕ
  lipschitzWindow : ℕ
  couplingSlack : ℕ
  couplingBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def BoundedLipschitzCouplingCertificateWindow.lipschitzControlled
    (w : BoundedLipschitzCouplingCertificateWindow) : Prop :=
  w.lipschitzWindow ≤ w.testWindow + w.couplingSlack + w.slack

def boundedLipschitzCouplingCertificateReady
    (w : BoundedLipschitzCouplingCertificateWindow) : Prop :=
  0 < w.testWindow ∧ w.lipschitzControlled ∧
    w.couplingBudget ≤ w.testWindow + w.lipschitzWindow + w.slack

def BoundedLipschitzCouplingCertificateWindow.certificate
    (w : BoundedLipschitzCouplingCertificateWindow) : ℕ :=
  w.testWindow + w.lipschitzWindow + w.couplingSlack + w.couplingBudget + w.slack

theorem boundedLipschitzCoupling_budget_le_certificate
    (w : BoundedLipschitzCouplingCertificateWindow) :
    w.couplingBudget ≤ w.certificate := by
  unfold BoundedLipschitzCouplingCertificateWindow.certificate
  omega

def sampleBoundedLipschitzCouplingCertificateWindow :
    BoundedLipschitzCouplingCertificateWindow :=
  { testWindow := 5, lipschitzWindow := 7, couplingSlack := 2,
    couplingBudget := 14, slack := 2 }

example : boundedLipschitzCouplingCertificateReady
    sampleBoundedLipschitzCouplingCertificateWindow := by
  norm_num [boundedLipschitzCouplingCertificateReady,
    BoundedLipschitzCouplingCertificateWindow.lipschitzControlled,
    sampleBoundedLipschitzCouplingCertificateWindow]


structure BoundedLipschitzCouplingWindowSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def BoundedLipschitzCouplingWindowSchemasBudgetCertificate.controlled
    (c : BoundedLipschitzCouplingWindowSchemasBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def BoundedLipschitzCouplingWindowSchemasBudgetCertificate.budgetControlled
    (c : BoundedLipschitzCouplingWindowSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def BoundedLipschitzCouplingWindowSchemasBudgetCertificate.Ready
    (c : BoundedLipschitzCouplingWindowSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def BoundedLipschitzCouplingWindowSchemasBudgetCertificate.size
    (c : BoundedLipschitzCouplingWindowSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem boundedLipschitzCouplingWindowSchemas_budgetCertificate_le_size
    (c : BoundedLipschitzCouplingWindowSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleBoundedLipschitzCouplingWindowSchemasBudgetCertificate :
    BoundedLipschitzCouplingWindowSchemasBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleBoundedLipschitzCouplingWindowSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [BoundedLipschitzCouplingWindowSchemasBudgetCertificate.controlled,
      sampleBoundedLipschitzCouplingWindowSchemasBudgetCertificate]
  · norm_num [BoundedLipschitzCouplingWindowSchemasBudgetCertificate.budgetControlled,
      sampleBoundedLipschitzCouplingWindowSchemasBudgetCertificate]

example : sampleBoundedLipschitzCouplingWindowSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [BoundedLipschitzCouplingWindowSchemasBudgetCertificate.controlled,
      sampleBoundedLipschitzCouplingWindowSchemasBudgetCertificate]
  · norm_num [BoundedLipschitzCouplingWindowSchemasBudgetCertificate.budgetControlled,
      sampleBoundedLipschitzCouplingWindowSchemasBudgetCertificate]

example :
    sampleBoundedLipschitzCouplingWindowSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleBoundedLipschitzCouplingWindowSchemasBudgetCertificate.size := by
  apply boundedLipschitzCouplingWindowSchemas_budgetCertificate_le_size
  constructor
  · norm_num [BoundedLipschitzCouplingWindowSchemasBudgetCertificate.controlled,
      sampleBoundedLipschitzCouplingWindowSchemasBudgetCertificate]
  · norm_num [BoundedLipschitzCouplingWindowSchemasBudgetCertificate.budgetControlled,
      sampleBoundedLipschitzCouplingWindowSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_le_size :
    sampleBoundedLipschitzCouplingWindowSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleBoundedLipschitzCouplingWindowSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady
    (data : List BoundedLipschitzCouplingWindowSchemasBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleBoundedLipschitzCouplingWindowSchemasBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleBoundedLipschitzCouplingWindowSchemasBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppC.BoundedLipschitzCouplingWindowSchemas
