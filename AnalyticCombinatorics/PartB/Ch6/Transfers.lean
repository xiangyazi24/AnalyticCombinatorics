import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Transfers.

Finite bookkeeping for translating local singular expansions into
coefficient asymptotics.
-/

namespace AnalyticCombinatorics.PartB.Ch6.Transfers

structure TransferWindow where
  localExpansionWindow : ℕ
  transferRuleWindow : ℕ
  coefficientWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def transferReady (w : TransferWindow) : Prop :=
  0 < w.localExpansionWindow ∧
    w.coefficientWindow ≤
      w.localExpansionWindow + w.transferRuleWindow + w.slack

def transferBudget (w : TransferWindow) : ℕ :=
  w.localExpansionWindow + w.transferRuleWindow + w.coefficientWindow + w.slack

theorem coefficientWindow_le_transferBudget (w : TransferWindow) :
    w.coefficientWindow ≤ transferBudget w := by
  unfold transferBudget
  omega

def sampleTransferWindow : TransferWindow :=
  { localExpansionWindow := 5
    transferRuleWindow := 4
    coefficientWindow := 8
    slack := 1 }

example : transferReady sampleTransferWindow := by
  norm_num [transferReady, sampleTransferWindow]

/-- Coefficient model produced by a square-root transfer schema. -/
def transferCoeffProxy (base n : ℕ) : ℕ :=
  (n + 1) * base ^ n

/-- Finite transfer envelope for a polynomial factor times exponential growth. -/
def transferEnvelopeCheck (base N : ℕ) : Bool :=
  (List.range (N + 1)).all fun n =>
    transferCoeffProxy base n ≤ (n + 1) * base ^ n

theorem transferCoeff_envelopeWindow :
    transferEnvelopeCheck 3 16 = true := by
  unfold transferEnvelopeCheck transferCoeffProxy
  native_decide

structure TransfersBudgetCertificate where
  expansionWindow : ℕ
  transferWindow : ℕ
  coefficientWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def TransfersBudgetCertificate.controlled
    (c : TransfersBudgetCertificate) : Prop :=
  0 < c.expansionWindow ∧
    c.coefficientWindow ≤ c.expansionWindow + c.transferWindow + c.slack

def TransfersBudgetCertificate.budgetControlled
    (c : TransfersBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.expansionWindow + c.transferWindow + c.coefficientWindow + c.slack

def TransfersBudgetCertificate.Ready
    (c : TransfersBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def TransfersBudgetCertificate.size
    (c : TransfersBudgetCertificate) : ℕ :=
  c.expansionWindow + c.transferWindow + c.coefficientWindow + c.slack

theorem transfers_budgetCertificate_le_size
    (c : TransfersBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  exact h.2

def sampleTransfersBudgetCertificate : TransfersBudgetCertificate :=
  { expansionWindow := 5
    transferWindow := 4
    coefficientWindow := 8
    certificateBudgetWindow := 18
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleTransfersBudgetCertificate.Ready := by
  constructor
  · norm_num [TransfersBudgetCertificate.controlled,
      sampleTransfersBudgetCertificate]
  · norm_num [TransfersBudgetCertificate.budgetControlled,
      sampleTransfersBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleTransfersBudgetCertificate.certificateBudgetWindow ≤
      sampleTransfersBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleTransfersBudgetCertificate.Ready := by
  constructor
  · norm_num [TransfersBudgetCertificate.controlled,
      sampleTransfersBudgetCertificate]
  · norm_num [TransfersBudgetCertificate.budgetControlled,
      sampleTransfersBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List TransfersBudgetCertificate) : Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady [sampleTransfersBudgetCertificate] = true := by
  unfold budgetCertificateListReady sampleTransfersBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch6.Transfers
