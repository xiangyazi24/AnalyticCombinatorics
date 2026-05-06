import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Multiple singularity window schemas.

The finite schema records singularity count, separation margin, and
transfer slack.
-/

namespace AnalyticCombinatorics.PartB.Ch6.MultipleSingularityWindowSchemas

structure MultipleSingularityWindowData where
  singularityCount : ℕ
  separationMargin : ℕ
  transferSlack : ℕ
deriving DecidableEq, Repr

def singularityCountPositive (d : MultipleSingularityWindowData) : Prop :=
  0 < d.singularityCount

def separationMarginControlled (d : MultipleSingularityWindowData) : Prop :=
  d.separationMargin ≤ d.singularityCount + d.transferSlack

def multipleSingularityWindowReady
    (d : MultipleSingularityWindowData) : Prop :=
  singularityCountPositive d ∧ separationMarginControlled d

def multipleSingularityWindowBudget
    (d : MultipleSingularityWindowData) : ℕ :=
  d.singularityCount + d.separationMargin + d.transferSlack

theorem multipleSingularityWindowReady.count
    {d : MultipleSingularityWindowData}
    (h : multipleSingularityWindowReady d) :
    singularityCountPositive d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem separationMargin_le_multipleSingularityBudget
    (d : MultipleSingularityWindowData) :
    d.separationMargin ≤ multipleSingularityWindowBudget d := by
  unfold multipleSingularityWindowBudget
  omega

def sampleMultipleSingularityWindowData :
    MultipleSingularityWindowData :=
  { singularityCount := 5, separationMargin := 7, transferSlack := 3 }

example :
    multipleSingularityWindowReady sampleMultipleSingularityWindowData := by
  norm_num [multipleSingularityWindowReady, singularityCountPositive]
  norm_num [separationMarginControlled, sampleMultipleSingularityWindowData]

example :
    multipleSingularityWindowBudget sampleMultipleSingularityWindowData = 15 := by
  native_decide


structure MultipleSingularityWindowSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def MultipleSingularityWindowSchemasBudgetCertificate.controlled
    (c : MultipleSingularityWindowSchemasBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def MultipleSingularityWindowSchemasBudgetCertificate.budgetControlled
    (c : MultipleSingularityWindowSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def MultipleSingularityWindowSchemasBudgetCertificate.Ready
    (c : MultipleSingularityWindowSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def MultipleSingularityWindowSchemasBudgetCertificate.size
    (c : MultipleSingularityWindowSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem multipleSingularityWindowSchemas_budgetCertificate_le_size
    (c : MultipleSingularityWindowSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleMultipleSingularityWindowSchemasBudgetCertificate :
    MultipleSingularityWindowSchemasBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleMultipleSingularityWindowSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [MultipleSingularityWindowSchemasBudgetCertificate.controlled,
      sampleMultipleSingularityWindowSchemasBudgetCertificate]
  · norm_num [MultipleSingularityWindowSchemasBudgetCertificate.budgetControlled,
      sampleMultipleSingularityWindowSchemasBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleMultipleSingularityWindowSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleMultipleSingularityWindowSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleMultipleSingularityWindowSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [MultipleSingularityWindowSchemasBudgetCertificate.controlled,
      sampleMultipleSingularityWindowSchemasBudgetCertificate]
  · norm_num [MultipleSingularityWindowSchemasBudgetCertificate.budgetControlled,
      sampleMultipleSingularityWindowSchemasBudgetCertificate]

example :
    sampleMultipleSingularityWindowSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleMultipleSingularityWindowSchemasBudgetCertificate.size := by
  apply multipleSingularityWindowSchemas_budgetCertificate_le_size
  constructor
  · norm_num [MultipleSingularityWindowSchemasBudgetCertificate.controlled,
      sampleMultipleSingularityWindowSchemasBudgetCertificate]
  · norm_num [MultipleSingularityWindowSchemasBudgetCertificate.budgetControlled,
      sampleMultipleSingularityWindowSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady
    (data : List MultipleSingularityWindowSchemasBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleMultipleSingularityWindowSchemasBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleMultipleSingularityWindowSchemasBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch6.MultipleSingularityWindowSchemas
