import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Exchangeable coupling schemas.

This module records finite bookkeeping for exchangeable couplings.
-/

namespace AnalyticCombinatorics.AppC.ExchangeableCouplingSchemas

structure ExchangeableCouplingData where
  exchangeableBlocks : ℕ
  couplingDefect : ℕ
  symmetrySlack : ℕ
deriving DecidableEq, Repr

def hasExchangeableBlocks (d : ExchangeableCouplingData) : Prop :=
  0 < d.exchangeableBlocks

def couplingDefectControlled (d : ExchangeableCouplingData) : Prop :=
  d.couplingDefect ≤ d.exchangeableBlocks + d.symmetrySlack

def exchangeableCouplingReady (d : ExchangeableCouplingData) : Prop :=
  hasExchangeableBlocks d ∧ couplingDefectControlled d

def exchangeableCouplingBudget (d : ExchangeableCouplingData) : ℕ :=
  d.exchangeableBlocks + d.couplingDefect + d.symmetrySlack

theorem exchangeableCouplingReady.hasExchangeableBlocks
    {d : ExchangeableCouplingData}
    (h : exchangeableCouplingReady d) :
    hasExchangeableBlocks d ∧ couplingDefectControlled d ∧
      d.couplingDefect ≤ exchangeableCouplingBudget d := by
  refine ⟨h.1, h.2, ?_⟩
  unfold exchangeableCouplingBudget
  omega

theorem couplingDefect_le_budget (d : ExchangeableCouplingData) :
    d.couplingDefect ≤ exchangeableCouplingBudget d := by
  unfold exchangeableCouplingBudget
  omega

def sampleExchangeableCouplingData : ExchangeableCouplingData :=
  { exchangeableBlocks := 6, couplingDefect := 8, symmetrySlack := 3 }

example : exchangeableCouplingReady sampleExchangeableCouplingData := by
  norm_num [exchangeableCouplingReady, hasExchangeableBlocks]
  norm_num [couplingDefectControlled, sampleExchangeableCouplingData]

example : exchangeableCouplingBudget sampleExchangeableCouplingData = 17 := by
  native_decide

structure ExchangeableCouplingWindow where
  blockWindow : ℕ
  defectWindow : ℕ
  symmetrySlack : ℕ
  couplingBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def ExchangeableCouplingWindow.defectControlled (w : ExchangeableCouplingWindow) : Prop :=
  w.defectWindow ≤ w.blockWindow + w.symmetrySlack + w.slack

def exchangeableCouplingWindowReady (w : ExchangeableCouplingWindow) : Prop :=
  0 < w.blockWindow ∧ w.defectControlled ∧
    w.couplingBudget ≤ w.blockWindow + w.defectWindow + w.slack

def ExchangeableCouplingWindow.certificate (w : ExchangeableCouplingWindow) : ℕ :=
  w.blockWindow + w.defectWindow + w.symmetrySlack + w.couplingBudget + w.slack

theorem exchangeableCoupling_couplingBudget_le_certificate
    (w : ExchangeableCouplingWindow) :
    w.couplingBudget ≤ w.certificate := by
  unfold ExchangeableCouplingWindow.certificate
  omega

def sampleExchangeableCouplingWindow : ExchangeableCouplingWindow :=
  { blockWindow := 5, defectWindow := 7, symmetrySlack := 2, couplingBudget := 14, slack := 2 }

example : exchangeableCouplingWindowReady sampleExchangeableCouplingWindow := by
  norm_num [exchangeableCouplingWindowReady, ExchangeableCouplingWindow.defectControlled,
    sampleExchangeableCouplingWindow]


structure ExchangeableCouplingSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def ExchangeableCouplingSchemasBudgetCertificate.controlled
    (c : ExchangeableCouplingSchemasBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def ExchangeableCouplingSchemasBudgetCertificate.budgetControlled
    (c : ExchangeableCouplingSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def ExchangeableCouplingSchemasBudgetCertificate.Ready
    (c : ExchangeableCouplingSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def ExchangeableCouplingSchemasBudgetCertificate.size
    (c : ExchangeableCouplingSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem exchangeableCouplingSchemas_budgetCertificate_le_size
    (c : ExchangeableCouplingSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleExchangeableCouplingSchemasBudgetCertificate :
    ExchangeableCouplingSchemasBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleExchangeableCouplingSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [ExchangeableCouplingSchemasBudgetCertificate.controlled,
      sampleExchangeableCouplingSchemasBudgetCertificate]
  · norm_num [ExchangeableCouplingSchemasBudgetCertificate.budgetControlled,
      sampleExchangeableCouplingSchemasBudgetCertificate]

example : sampleExchangeableCouplingSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [ExchangeableCouplingSchemasBudgetCertificate.controlled,
      sampleExchangeableCouplingSchemasBudgetCertificate]
  · norm_num [ExchangeableCouplingSchemasBudgetCertificate.budgetControlled,
      sampleExchangeableCouplingSchemasBudgetCertificate]

example :
    sampleExchangeableCouplingSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleExchangeableCouplingSchemasBudgetCertificate.size := by
  apply exchangeableCouplingSchemas_budgetCertificate_le_size
  constructor
  · norm_num [ExchangeableCouplingSchemasBudgetCertificate.controlled,
      sampleExchangeableCouplingSchemasBudgetCertificate]
  · norm_num [ExchangeableCouplingSchemasBudgetCertificate.budgetControlled,
      sampleExchangeableCouplingSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_le_size :
    sampleExchangeableCouplingSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleExchangeableCouplingSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List ExchangeableCouplingSchemasBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleExchangeableCouplingSchemasBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleExchangeableCouplingSchemasBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppC.ExchangeableCouplingSchemas
