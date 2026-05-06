import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Transfer-Tauberian comparison windows.

This module records finite bookkeeping for comparing transfer and Tauberian
windows.
-/

namespace AnalyticCombinatorics.Asymptotics.TransferTauberianComparisonWindows

structure TransferTauberianComparisonData where
  transferScale : ℕ
  tauberianScale : ℕ
  comparisonSlack : ℕ
deriving DecidableEq, Repr

def hasTransferScale (d : TransferTauberianComparisonData) : Prop :=
  0 < d.transferScale

def tauberianScaleControlled
    (d : TransferTauberianComparisonData) : Prop :=
  d.tauberianScale ≤ d.transferScale + d.comparisonSlack

def transferTauberianComparisonReady
    (d : TransferTauberianComparisonData) : Prop :=
  hasTransferScale d ∧ tauberianScaleControlled d

def transferTauberianComparisonBudget
    (d : TransferTauberianComparisonData) : ℕ :=
  d.transferScale + d.tauberianScale + d.comparisonSlack

theorem transferTauberianComparisonReady.hasTransferScale
    {d : TransferTauberianComparisonData}
    (h : transferTauberianComparisonReady d) :
    hasTransferScale d ∧ tauberianScaleControlled d ∧
      d.tauberianScale ≤ transferTauberianComparisonBudget d := by
  refine ⟨h.1, h.2, ?_⟩
  unfold transferTauberianComparisonBudget
  omega

theorem tauberianScale_le_budget
    (d : TransferTauberianComparisonData) :
    d.tauberianScale ≤ transferTauberianComparisonBudget d := by
  unfold transferTauberianComparisonBudget
  omega

def sampleTransferTauberianComparisonData :
    TransferTauberianComparisonData :=
  { transferScale := 7, tauberianScale := 9, comparisonSlack := 3 }

example : transferTauberianComparisonReady
    sampleTransferTauberianComparisonData := by
  norm_num [transferTauberianComparisonReady, hasTransferScale]
  norm_num
    [tauberianScaleControlled, sampleTransferTauberianComparisonData]

example :
    transferTauberianComparisonBudget
      sampleTransferTauberianComparisonData = 19 := by
  native_decide

/-- Finite executable readiness audit for transfer-Tauberian comparison data. -/
def transferTauberianComparisonDataListReady
    (data : List TransferTauberianComparisonData) : Bool :=
  data.all fun d =>
    0 < d.transferScale && d.tauberianScale ≤ d.transferScale + d.comparisonSlack

theorem transferTauberianComparisonDataList_readyWindow :
    transferTauberianComparisonDataListReady
      [{ transferScale := 4, tauberianScale := 5, comparisonSlack := 1 },
       { transferScale := 7, tauberianScale := 9, comparisonSlack := 3 }] =
      true := by
  unfold transferTauberianComparisonDataListReady
  native_decide

/-- A certificate window for transfer-Tauberian comparison. -/
structure TransferTauberianComparisonCertificateWindow where
  transferWindow : ℕ
  tauberianWindow : ℕ
  comparisonSlack : ℕ
  certificateBudget : ℕ
  slack : ℕ

/-- The Tauberian window is controlled by the transfer window. -/
def transferTauberianComparisonCertificateControlled
    (w : TransferTauberianComparisonCertificateWindow) : Prop :=
  w.tauberianWindow ≤ w.transferWindow + w.comparisonSlack + w.slack

/-- Readiness for a transfer-Tauberian comparison certificate. -/
def transferTauberianComparisonCertificateReady
    (w : TransferTauberianComparisonCertificateWindow) : Prop :=
  0 < w.transferWindow ∧
    transferTauberianComparisonCertificateControlled w ∧
      w.certificateBudget ≤ w.transferWindow + w.tauberianWindow + w.slack

/-- Total size of a transfer-Tauberian comparison certificate. -/
def transferTauberianComparisonCertificate
    (w : TransferTauberianComparisonCertificateWindow) : ℕ :=
  w.transferWindow + w.tauberianWindow + w.comparisonSlack +
    w.certificateBudget + w.slack

theorem transferTauberianComparisonCertificate_budget_le_certificate
    (w : TransferTauberianComparisonCertificateWindow)
    (h : transferTauberianComparisonCertificateReady w) :
    w.certificateBudget ≤ transferTauberianComparisonCertificate w := by
  rcases h with ⟨_, _, hbudget⟩
  unfold transferTauberianComparisonCertificate
  omega

def sampleTransferTauberianComparisonCertificateWindow :
    TransferTauberianComparisonCertificateWindow where
  transferWindow := 7
  tauberianWindow := 8
  comparisonSlack := 2
  certificateBudget := 14
  slack := 1

example :
    transferTauberianComparisonCertificateReady
      sampleTransferTauberianComparisonCertificateWindow := by
  norm_num [transferTauberianComparisonCertificateReady,
    transferTauberianComparisonCertificateControlled,
    sampleTransferTauberianComparisonCertificateWindow]

example :
    sampleTransferTauberianComparisonCertificateWindow.certificateBudget ≤
      transferTauberianComparisonCertificate
        sampleTransferTauberianComparisonCertificateWindow := by
  apply transferTauberianComparisonCertificate_budget_le_certificate
  norm_num [transferTauberianComparisonCertificateReady,
    transferTauberianComparisonCertificateControlled,
    sampleTransferTauberianComparisonCertificateWindow]

structure TransferTauberianComparisonRefinementCertificate where
  transferWindow : ℕ
  tauberianWindow : ℕ
  comparisonSlackWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def TransferTauberianComparisonRefinementCertificate.tauberianControlled
    (c : TransferTauberianComparisonRefinementCertificate) : Prop :=
  c.tauberianWindow ≤ c.transferWindow + c.comparisonSlackWindow + c.slack

def TransferTauberianComparisonRefinementCertificate.certificateBudgetControlled
    (c : TransferTauberianComparisonRefinementCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.transferWindow + c.tauberianWindow + c.comparisonSlackWindow + c.slack

def transferTauberianComparisonRefinementReady
    (c : TransferTauberianComparisonRefinementCertificate) : Prop :=
  0 < c.transferWindow ∧ c.tauberianControlled ∧ c.certificateBudgetControlled

def TransferTauberianComparisonRefinementCertificate.size
    (c : TransferTauberianComparisonRefinementCertificate) : ℕ :=
  c.transferWindow + c.tauberianWindow + c.comparisonSlackWindow + c.slack

theorem transferTauberianComparison_certificateBudgetWindow_le_size
    {c : TransferTauberianComparisonRefinementCertificate}
    (h : transferTauberianComparisonRefinementReady c) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, _, hbudget⟩
  exact hbudget

def sampleTransferTauberianComparisonRefinementCertificate :
    TransferTauberianComparisonRefinementCertificate :=
  { transferWindow := 7, tauberianWindow := 8, comparisonSlackWindow := 2,
    certificateBudgetWindow := 18, slack := 1 }

example : transferTauberianComparisonRefinementReady
    sampleTransferTauberianComparisonRefinementCertificate := by
  norm_num [transferTauberianComparisonRefinementReady,
    TransferTauberianComparisonRefinementCertificate.tauberianControlled,
    TransferTauberianComparisonRefinementCertificate.certificateBudgetControlled,
    sampleTransferTauberianComparisonRefinementCertificate]

example :
    sampleTransferTauberianComparisonRefinementCertificate.certificateBudgetWindow ≤
      sampleTransferTauberianComparisonRefinementCertificate.size := by
  norm_num [TransferTauberianComparisonRefinementCertificate.size,
    sampleTransferTauberianComparisonRefinementCertificate]

structure TransferTauberianComparisonBudgetCertificate where
  transferWindow : ℕ
  tauberianWindow : ℕ
  comparisonSlackWindow : ℕ
  comparisonBudgetWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def TransferTauberianComparisonBudgetCertificate.controlled
    (c : TransferTauberianComparisonBudgetCertificate) : Prop :=
  0 < c.transferWindow ∧
    c.tauberianWindow ≤ c.transferWindow + c.comparisonSlackWindow + c.slack ∧
      c.comparisonBudgetWindow ≤
        c.transferWindow + c.tauberianWindow + c.comparisonSlackWindow + c.slack

def TransferTauberianComparisonBudgetCertificate.budgetControlled
    (c : TransferTauberianComparisonBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.transferWindow + c.tauberianWindow + c.comparisonSlackWindow +
      c.comparisonBudgetWindow + c.slack

def TransferTauberianComparisonBudgetCertificate.Ready
    (c : TransferTauberianComparisonBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def TransferTauberianComparisonBudgetCertificate.size
    (c : TransferTauberianComparisonBudgetCertificate) : ℕ :=
  c.transferWindow + c.tauberianWindow + c.comparisonSlackWindow +
    c.comparisonBudgetWindow + c.slack

theorem transferTauberianComparison_budgetCertificate_le_size
    (c : TransferTauberianComparisonBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleTransferTauberianComparisonBudgetCertificate :
    TransferTauberianComparisonBudgetCertificate :=
  { transferWindow := 7
    tauberianWindow := 8
    comparisonSlackWindow := 2
    comparisonBudgetWindow := 18
    certificateBudgetWindow := 36
    slack := 1 }

example : sampleTransferTauberianComparisonBudgetCertificate.Ready := by
  constructor
  · norm_num [TransferTauberianComparisonBudgetCertificate.controlled,
      sampleTransferTauberianComparisonBudgetCertificate]
  · norm_num [TransferTauberianComparisonBudgetCertificate.budgetControlled,
      sampleTransferTauberianComparisonBudgetCertificate]

example :
    sampleTransferTauberianComparisonBudgetCertificate.certificateBudgetWindow ≤
      sampleTransferTauberianComparisonBudgetCertificate.size := by
  apply transferTauberianComparison_budgetCertificate_le_size
  constructor
  · norm_num [TransferTauberianComparisonBudgetCertificate.controlled,
      sampleTransferTauberianComparisonBudgetCertificate]
  · norm_num [TransferTauberianComparisonBudgetCertificate.budgetControlled,
      sampleTransferTauberianComparisonBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleTransferTauberianComparisonBudgetCertificate.Ready := by
  constructor
  · norm_num [TransferTauberianComparisonBudgetCertificate.controlled,
      sampleTransferTauberianComparisonBudgetCertificate]
  · norm_num [TransferTauberianComparisonBudgetCertificate.budgetControlled,
      sampleTransferTauberianComparisonBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleTransferTauberianComparisonBudgetCertificate.certificateBudgetWindow ≤
      sampleTransferTauberianComparisonBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady
    (data : List TransferTauberianComparisonBudgetCertificate) : Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleTransferTauberianComparisonBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleTransferTauberianComparisonBudgetCertificate
  native_decide

end AnalyticCombinatorics.Asymptotics.TransferTauberianComparisonWindows
