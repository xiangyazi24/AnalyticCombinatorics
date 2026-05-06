import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Exchangeable limit schemas.

The finite schema records block count, symmetry budget, and approximation
slack.
-/

namespace AnalyticCombinatorics.AppC.ExchangeableLimitSchemas

structure ExchangeableLimitData where
  blockCount : ℕ
  symmetryBudget : ℕ
  approximationSlack : ℕ
deriving DecidableEq, Repr

def blockCountPositive (d : ExchangeableLimitData) : Prop :=
  0 < d.blockCount

def symmetryControlled (d : ExchangeableLimitData) : Prop :=
  d.symmetryBudget ≤ d.blockCount + d.approximationSlack

def exchangeableLimitReady (d : ExchangeableLimitData) : Prop :=
  blockCountPositive d ∧ symmetryControlled d

def exchangeableLimitBudget (d : ExchangeableLimitData) : ℕ :=
  d.blockCount + d.symmetryBudget + d.approximationSlack

theorem exchangeableLimitReady.blocks {d : ExchangeableLimitData}
    (h : exchangeableLimitReady d) :
    blockCountPositive d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem symmetryBudget_le_exchangeableLimitBudget
    (d : ExchangeableLimitData) :
    d.symmetryBudget ≤ exchangeableLimitBudget d := by
  unfold exchangeableLimitBudget
  omega

def sampleExchangeableLimitData : ExchangeableLimitData :=
  { blockCount := 6, symmetryBudget := 8, approximationSlack := 3 }

example : exchangeableLimitReady sampleExchangeableLimitData := by
  norm_num [exchangeableLimitReady, blockCountPositive]
  norm_num [symmetryControlled, sampleExchangeableLimitData]

example : exchangeableLimitBudget sampleExchangeableLimitData = 17 := by
  native_decide

structure ExchangeableLimitWindow where
  blockWindow : ℕ
  symmetryWindow : ℕ
  approximationSlack : ℕ
  limitBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def ExchangeableLimitWindow.symmetryControlled (w : ExchangeableLimitWindow) : Prop :=
  w.symmetryWindow ≤ w.blockWindow + w.approximationSlack + w.slack

def exchangeableLimitWindowReady (w : ExchangeableLimitWindow) : Prop :=
  0 < w.blockWindow ∧ w.symmetryControlled ∧
    w.limitBudget ≤ w.blockWindow + w.symmetryWindow + w.slack

def ExchangeableLimitWindow.certificate (w : ExchangeableLimitWindow) : ℕ :=
  w.blockWindow + w.symmetryWindow + w.approximationSlack + w.limitBudget + w.slack

theorem exchangeableLimit_limitBudget_le_certificate (w : ExchangeableLimitWindow) :
    w.limitBudget ≤ w.certificate := by
  unfold ExchangeableLimitWindow.certificate
  omega

def sampleExchangeableLimitWindow : ExchangeableLimitWindow :=
  { blockWindow := 5, symmetryWindow := 7, approximationSlack := 2, limitBudget := 14, slack := 2 }

example : exchangeableLimitWindowReady sampleExchangeableLimitWindow := by
  norm_num [exchangeableLimitWindowReady, ExchangeableLimitWindow.symmetryControlled,
    sampleExchangeableLimitWindow]


structure ExchangeableLimitSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def ExchangeableLimitSchemasBudgetCertificate.controlled
    (c : ExchangeableLimitSchemasBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def ExchangeableLimitSchemasBudgetCertificate.budgetControlled
    (c : ExchangeableLimitSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def ExchangeableLimitSchemasBudgetCertificate.Ready
    (c : ExchangeableLimitSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def ExchangeableLimitSchemasBudgetCertificate.size
    (c : ExchangeableLimitSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem exchangeableLimitSchemas_budgetCertificate_le_size
    (c : ExchangeableLimitSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleExchangeableLimitSchemasBudgetCertificate :
    ExchangeableLimitSchemasBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleExchangeableLimitSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [ExchangeableLimitSchemasBudgetCertificate.controlled,
      sampleExchangeableLimitSchemasBudgetCertificate]
  · norm_num [ExchangeableLimitSchemasBudgetCertificate.budgetControlled,
      sampleExchangeableLimitSchemasBudgetCertificate]

example : sampleExchangeableLimitSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [ExchangeableLimitSchemasBudgetCertificate.controlled,
      sampleExchangeableLimitSchemasBudgetCertificate]
  · norm_num [ExchangeableLimitSchemasBudgetCertificate.budgetControlled,
      sampleExchangeableLimitSchemasBudgetCertificate]

example :
    sampleExchangeableLimitSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleExchangeableLimitSchemasBudgetCertificate.size := by
  apply exchangeableLimitSchemas_budgetCertificate_le_size
  constructor
  · norm_num [ExchangeableLimitSchemasBudgetCertificate.controlled,
      sampleExchangeableLimitSchemasBudgetCertificate]
  · norm_num [ExchangeableLimitSchemasBudgetCertificate.budgetControlled,
      sampleExchangeableLimitSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_le_size :
    sampleExchangeableLimitSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleExchangeableLimitSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List ExchangeableLimitSchemasBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleExchangeableLimitSchemasBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleExchangeableLimitSchemasBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppC.ExchangeableLimitSchemas
