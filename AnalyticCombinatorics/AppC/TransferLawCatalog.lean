import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Catalog entries for universal transfer laws.

Each entry records the hypotheses that connect an analytic schema to a
coefficient-level limit law.
-/

namespace AnalyticCombinatorics.AppC.TransferLawCatalog

structure UniversalTransferLaw where
  analyticSchema : Prop
  positivity : Prop
  errorTight : Prop

def lawReady (law : UniversalTransferLaw) : Prop :=
  law.analyticSchema ∧ law.positivity ∧ law.errorTight

def errorBudget (mainTerm remainder : ℕ) : ℕ :=
  mainTerm + remainder

theorem lawReady_intro {law : UniversalTransferLaw}
    (ha : law.analyticSchema) (hp : law.positivity) (he : law.errorTight) :
    lawReady law := by
  exact ⟨ha, hp, he⟩

theorem lawReady.error {law : UniversalTransferLaw}
    (h : lawReady law) :
    law.errorTight := h.2.2

theorem errorBudget_mono {a b c d : ℕ}
    (hab : a ≤ b) (hcd : c ≤ d) :
    errorBudget a c ≤ errorBudget b d := by
  unfold errorBudget
  omega

def sampleLaw : UniversalTransferLaw :=
  { analyticSchema := errorBudget 10 3 = 13
    positivity := ∀ n : Fin 5, 0 < n.val + 1
    errorTight := 3 ≤ 10 }

example : lawReady sampleLaw := by
  unfold lawReady sampleLaw
  constructor
  · native_decide
  · constructor
    · intro n
      omega
    · norm_num

example : errorBudget 10 3 = 13 := by
  native_decide

structure TransferLawWindow where
  analyticWindow : ℕ
  positivityWindow : ℕ
  errorWindow : ℕ
  transferBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def TransferLawWindow.errorControlled (w : TransferLawWindow) : Prop :=
  w.errorWindow ≤ w.analyticWindow + w.positivityWindow + w.slack

def transferLawWindowReady (w : TransferLawWindow) : Prop :=
  0 < w.analyticWindow ∧ w.errorControlled ∧
    w.transferBudget ≤ w.analyticWindow + w.positivityWindow + w.errorWindow + w.slack

def TransferLawWindow.certificate (w : TransferLawWindow) : ℕ :=
  w.analyticWindow + w.positivityWindow + w.errorWindow + w.transferBudget + w.slack

theorem transferLaw_transferBudget_le_certificate (w : TransferLawWindow) :
    w.transferBudget ≤ w.certificate := by
  unfold TransferLawWindow.certificate
  omega

def sampleTransferLawWindow : TransferLawWindow :=
  { analyticWindow := 5, positivityWindow := 3, errorWindow := 4,
    transferBudget := 13, slack := 1 }

example : transferLawWindowReady sampleTransferLawWindow := by
  norm_num [transferLawWindowReady, TransferLawWindow.errorControlled,
    sampleTransferLawWindow]


structure TransferLawCatalogBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def TransferLawCatalogBudgetCertificate.controlled
    (c : TransferLawCatalogBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def TransferLawCatalogBudgetCertificate.budgetControlled
    (c : TransferLawCatalogBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def TransferLawCatalogBudgetCertificate.Ready
    (c : TransferLawCatalogBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def TransferLawCatalogBudgetCertificate.size
    (c : TransferLawCatalogBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem transferLawCatalog_budgetCertificate_le_size
    (c : TransferLawCatalogBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleTransferLawCatalogBudgetCertificate :
    TransferLawCatalogBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

example : sampleTransferLawCatalogBudgetCertificate.Ready := by
  constructor
  · norm_num [TransferLawCatalogBudgetCertificate.controlled,
      sampleTransferLawCatalogBudgetCertificate]
  · norm_num [TransferLawCatalogBudgetCertificate.budgetControlled,
      sampleTransferLawCatalogBudgetCertificate]

example :
    sampleTransferLawCatalogBudgetCertificate.certificateBudgetWindow ≤
      sampleTransferLawCatalogBudgetCertificate.size := by
  apply transferLawCatalog_budgetCertificate_le_size
  constructor
  · norm_num [TransferLawCatalogBudgetCertificate.controlled,
      sampleTransferLawCatalogBudgetCertificate]
  · norm_num [TransferLawCatalogBudgetCertificate.budgetControlled,
      sampleTransferLawCatalogBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleTransferLawCatalogBudgetCertificate.Ready := by
  constructor
  · norm_num [TransferLawCatalogBudgetCertificate.controlled,
      sampleTransferLawCatalogBudgetCertificate]
  · norm_num [TransferLawCatalogBudgetCertificate.budgetControlled,
      sampleTransferLawCatalogBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleTransferLawCatalogBudgetCertificate.certificateBudgetWindow ≤
      sampleTransferLawCatalogBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List TransferLawCatalogBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleTransferLawCatalogBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleTransferLawCatalogBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppC.TransferLawCatalog
