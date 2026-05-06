import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Conditional limit schemas.

The finite record stores conditioning events, sample budget, and
normalization slack.
-/

namespace AnalyticCombinatorics.AppC.ConditionalLimitSchemas

structure ConditionalLimitData where
  conditioningEvents : ℕ
  sampleBudget : ℕ
  normalizationSlack : ℕ
deriving DecidableEq, Repr

def sampleBudgetPositive (d : ConditionalLimitData) : Prop :=
  0 < d.sampleBudget

def conditioningControlled (d : ConditionalLimitData) : Prop :=
  d.conditioningEvents ≤ d.sampleBudget + d.normalizationSlack

def conditionalLimitReady (d : ConditionalLimitData) : Prop :=
  sampleBudgetPositive d ∧ conditioningControlled d

def conditionalLimitBudget (d : ConditionalLimitData) : ℕ :=
  d.conditioningEvents + d.sampleBudget + d.normalizationSlack

theorem conditionalLimitReady.sample {d : ConditionalLimitData}
    (h : conditionalLimitReady d) :
    sampleBudgetPositive d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem conditioningEvents_le_conditionalLimitBudget
    (d : ConditionalLimitData) :
    d.conditioningEvents ≤ conditionalLimitBudget d := by
  unfold conditionalLimitBudget
  omega

def sampleConditionalLimitData : ConditionalLimitData :=
  { conditioningEvents := 6, sampleBudget := 4, normalizationSlack := 3 }

example : conditionalLimitReady sampleConditionalLimitData := by
  norm_num [conditionalLimitReady, sampleBudgetPositive]
  norm_num [conditioningControlled, sampleConditionalLimitData]

example : conditionalLimitBudget sampleConditionalLimitData = 13 := by
  native_decide

structure ConditionalLimitWindow where
  eventWindow : ℕ
  sampleWindow : ℕ
  normalizationSlack : ℕ
  limitBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def ConditionalLimitWindow.eventsControlled (w : ConditionalLimitWindow) : Prop :=
  w.eventWindow ≤ w.sampleWindow + w.normalizationSlack + w.slack

def conditionalLimitWindowReady (w : ConditionalLimitWindow) : Prop :=
  0 < w.sampleWindow ∧ w.eventsControlled ∧
    w.limitBudget ≤ w.eventWindow + w.sampleWindow + w.slack

def ConditionalLimitWindow.certificate (w : ConditionalLimitWindow) : ℕ :=
  w.eventWindow + w.sampleWindow + w.normalizationSlack + w.limitBudget + w.slack

theorem conditionalLimit_limitBudget_le_certificate (w : ConditionalLimitWindow) :
    w.limitBudget ≤ w.certificate := by
  unfold ConditionalLimitWindow.certificate
  omega

def sampleConditionalLimitWindow : ConditionalLimitWindow :=
  { eventWindow := 5, sampleWindow := 4, normalizationSlack := 2, limitBudget := 10, slack := 1 }

example : conditionalLimitWindowReady sampleConditionalLimitWindow := by
  norm_num [conditionalLimitWindowReady, ConditionalLimitWindow.eventsControlled,
    sampleConditionalLimitWindow]


structure ConditionalLimitSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def ConditionalLimitSchemasBudgetCertificate.controlled
    (c : ConditionalLimitSchemasBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def ConditionalLimitSchemasBudgetCertificate.budgetControlled
    (c : ConditionalLimitSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def ConditionalLimitSchemasBudgetCertificate.Ready
    (c : ConditionalLimitSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def ConditionalLimitSchemasBudgetCertificate.size
    (c : ConditionalLimitSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem conditionalLimitSchemas_budgetCertificate_le_size
    (c : ConditionalLimitSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleConditionalLimitSchemasBudgetCertificate :
    ConditionalLimitSchemasBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleConditionalLimitSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [ConditionalLimitSchemasBudgetCertificate.controlled,
      sampleConditionalLimitSchemasBudgetCertificate]
  · norm_num [ConditionalLimitSchemasBudgetCertificate.budgetControlled,
      sampleConditionalLimitSchemasBudgetCertificate]

example : sampleConditionalLimitSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [ConditionalLimitSchemasBudgetCertificate.controlled,
      sampleConditionalLimitSchemasBudgetCertificate]
  · norm_num [ConditionalLimitSchemasBudgetCertificate.budgetControlled,
      sampleConditionalLimitSchemasBudgetCertificate]

example :
    sampleConditionalLimitSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleConditionalLimitSchemasBudgetCertificate.size := by
  apply conditionalLimitSchemas_budgetCertificate_le_size
  constructor
  · norm_num [ConditionalLimitSchemasBudgetCertificate.controlled,
      sampleConditionalLimitSchemasBudgetCertificate]
  · norm_num [ConditionalLimitSchemasBudgetCertificate.budgetControlled,
      sampleConditionalLimitSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_le_size :
    sampleConditionalLimitSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleConditionalLimitSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List ConditionalLimitSchemasBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleConditionalLimitSchemasBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleConditionalLimitSchemasBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppC.ConditionalLimitSchemas
