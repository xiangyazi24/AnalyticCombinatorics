import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Threshold transfer schemas.

The finite data tracks a threshold and a two-sided window around it.
-/

namespace AnalyticCombinatorics.Asymptotics.ThresholdTransferSchemas

structure ThresholdTransferData where
  threshold : ℕ
  lowerWindow : ℕ
  upperWindow : ℕ
deriving DecidableEq, Repr

def lowerWindowWithinThreshold (d : ThresholdTransferData) : Prop :=
  d.lowerWindow ≤ d.threshold

def thresholdWithinUpperWindow (d : ThresholdTransferData) : Prop :=
  d.threshold ≤ d.upperWindow + d.lowerWindow

def thresholdTransferReady (d : ThresholdTransferData) : Prop :=
  lowerWindowWithinThreshold d ∧ thresholdWithinUpperWindow d

def thresholdTransferBudget (d : ThresholdTransferData) : ℕ :=
  d.threshold + d.lowerWindow + d.upperWindow

theorem thresholdTransferReady.lower {d : ThresholdTransferData}
    (h : thresholdTransferReady d) :
    lowerWindowWithinThreshold d ∧ thresholdWithinUpperWindow d ∧
      d.threshold ≤ thresholdTransferBudget d := by
  refine ⟨h.1, h.2, ?_⟩
  unfold thresholdTransferBudget
  omega

theorem threshold_le_transferBudget (d : ThresholdTransferData) :
    d.threshold ≤ thresholdTransferBudget d := by
  unfold thresholdTransferBudget
  omega

def sampleThresholdTransferData : ThresholdTransferData :=
  { threshold := 8, lowerWindow := 3, upperWindow := 6 }

example : thresholdTransferReady sampleThresholdTransferData := by
  norm_num [thresholdTransferReady, lowerWindowWithinThreshold]
  norm_num [thresholdWithinUpperWindow, sampleThresholdTransferData]

example : thresholdTransferBudget sampleThresholdTransferData = 17 := by
  native_decide

/-- Finite executable readiness audit for threshold transfer data. -/
def thresholdTransferDataListReady
    (data : List ThresholdTransferData) : Bool :=
  data.all fun d =>
    d.lowerWindow ≤ d.threshold && d.threshold ≤ d.upperWindow + d.lowerWindow

theorem thresholdTransferDataList_readyWindow :
    thresholdTransferDataListReady
      [{ threshold := 5, lowerWindow := 2, upperWindow := 4 },
       { threshold := 8, lowerWindow := 3, upperWindow := 6 }] = true := by
  unfold thresholdTransferDataListReady
  native_decide

structure ThresholdTransferWindow where
  thresholdWindow : ℕ
  lowerWindow : ℕ
  upperWindow : ℕ
  transferBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def ThresholdTransferWindow.thresholdControlled
    (w : ThresholdTransferWindow) : Prop :=
  w.lowerWindow ≤ w.thresholdWindow ∧
    w.thresholdWindow ≤ w.upperWindow + w.lowerWindow + w.slack

def thresholdTransferWindowReady (w : ThresholdTransferWindow) : Prop :=
  w.thresholdControlled ∧
    w.transferBudget ≤ w.thresholdWindow + w.lowerWindow + w.upperWindow + w.slack

def ThresholdTransferWindow.certificate (w : ThresholdTransferWindow) : ℕ :=
  w.thresholdWindow + w.lowerWindow + w.upperWindow + w.transferBudget + w.slack

theorem thresholdTransfer_transferBudget_le_certificate
    (w : ThresholdTransferWindow) :
    w.transferBudget ≤ w.certificate := by
  unfold ThresholdTransferWindow.certificate
  omega

def sampleThresholdTransferWindow : ThresholdTransferWindow :=
  { thresholdWindow := 8, lowerWindow := 3, upperWindow := 6,
    transferBudget := 18, slack := 1 }

example : thresholdTransferWindowReady sampleThresholdTransferWindow := by
  norm_num [thresholdTransferWindowReady,
    ThresholdTransferWindow.thresholdControlled, sampleThresholdTransferWindow]

/-- A refinement certificate for threshold transfer windows. -/
structure ThresholdTransferCertificate where
  thresholdWindow : ℕ
  lowerWindow : ℕ
  upperWindow : ℕ
  transferBudgetWindow : ℕ
  slack : ℕ

/-- Threshold and transfer windows are two-sided controlled. -/
def thresholdTransferCertificateControlled
    (w : ThresholdTransferCertificate) : Prop :=
  w.lowerWindow ≤ w.thresholdWindow ∧
    w.thresholdWindow ≤ w.upperWindow + w.lowerWindow + w.slack ∧
      w.transferBudgetWindow ≤
        w.thresholdWindow + w.lowerWindow + w.upperWindow + w.slack

/-- Readiness for a threshold transfer certificate. -/
def thresholdTransferCertificateReady
    (w : ThresholdTransferCertificate) : Prop :=
  thresholdTransferCertificateControlled w ∧
    w.transferBudgetWindow ≤
      w.thresholdWindow + w.lowerWindow + w.upperWindow +
        w.transferBudgetWindow + w.slack

/-- Total size of a threshold transfer certificate. -/
def thresholdTransferCertificateSize
    (w : ThresholdTransferCertificate) : ℕ :=
  w.thresholdWindow + w.lowerWindow + w.upperWindow +
    w.transferBudgetWindow + w.slack

theorem thresholdTransferCertificate_budget_le_size
    (w : ThresholdTransferCertificate)
    (h : thresholdTransferCertificateReady w) :
    w.transferBudgetWindow ≤ thresholdTransferCertificateSize w := by
  rcases h with ⟨_, hbudget⟩
  unfold thresholdTransferCertificateSize
  omega

def sampleThresholdTransferCertificate :
    ThresholdTransferCertificate where
  thresholdWindow := 8
  lowerWindow := 3
  upperWindow := 6
  transferBudgetWindow := 18
  slack := 1

example :
    thresholdTransferCertificateReady sampleThresholdTransferCertificate := by
  norm_num [thresholdTransferCertificateReady,
    thresholdTransferCertificateControlled, sampleThresholdTransferCertificate]

example :
    sampleThresholdTransferCertificate.transferBudgetWindow ≤
      thresholdTransferCertificateSize sampleThresholdTransferCertificate := by
  apply thresholdTransferCertificate_budget_le_size
  norm_num [thresholdTransferCertificateReady,
    thresholdTransferCertificateControlled, sampleThresholdTransferCertificate]

/-- A refinement certificate with the threshold-transfer budget separated from size. -/
structure ThresholdTransferRefinementCertificate where
  thresholdWindow : ℕ
  lowerWindow : ℕ
  upperWindow : ℕ
  transferBudgetWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def ThresholdTransferRefinementCertificate.thresholdControlled
    (cert : ThresholdTransferRefinementCertificate) : Prop :=
  cert.lowerWindow ≤ cert.thresholdWindow ∧
    cert.thresholdWindow ≤ cert.upperWindow + cert.lowerWindow + cert.slack ∧
      cert.transferBudgetWindow ≤
        cert.thresholdWindow + cert.lowerWindow + cert.upperWindow + cert.slack

def ThresholdTransferRefinementCertificate.budgetControlled
    (cert : ThresholdTransferRefinementCertificate) : Prop :=
  cert.certificateBudgetWindow ≤
    cert.thresholdWindow + cert.lowerWindow + cert.upperWindow +
      cert.transferBudgetWindow + cert.slack

def thresholdTransferRefinementReady
    (cert : ThresholdTransferRefinementCertificate) : Prop :=
  cert.thresholdControlled ∧ cert.budgetControlled

def ThresholdTransferRefinementCertificate.size
    (cert : ThresholdTransferRefinementCertificate) : ℕ :=
  cert.thresholdWindow + cert.lowerWindow + cert.upperWindow +
    cert.transferBudgetWindow + cert.slack

theorem thresholdTransfer_certificateBudgetWindow_le_size
    (cert : ThresholdTransferRefinementCertificate)
    (h : thresholdTransferRefinementReady cert) :
    cert.certificateBudgetWindow ≤ cert.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleThresholdTransferRefinementCertificate :
    ThresholdTransferRefinementCertificate :=
  { thresholdWindow := 8, lowerWindow := 3, upperWindow := 6,
    transferBudgetWindow := 18, certificateBudgetWindow := 36, slack := 1 }

example :
    thresholdTransferRefinementReady sampleThresholdTransferRefinementCertificate := by
  norm_num [thresholdTransferRefinementReady,
    ThresholdTransferRefinementCertificate.thresholdControlled,
    ThresholdTransferRefinementCertificate.budgetControlled,
    sampleThresholdTransferRefinementCertificate]

example :
    sampleThresholdTransferRefinementCertificate.certificateBudgetWindow ≤
      sampleThresholdTransferRefinementCertificate.size := by
  apply thresholdTransfer_certificateBudgetWindow_le_size
  norm_num [thresholdTransferRefinementReady,
    ThresholdTransferRefinementCertificate.thresholdControlled,
    ThresholdTransferRefinementCertificate.budgetControlled,
    sampleThresholdTransferRefinementCertificate]


structure ThresholdTransferSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def ThresholdTransferSchemasBudgetCertificate.controlled
    (c : ThresholdTransferSchemasBudgetCertificate) : Prop :=
  0 < c.primaryWindow ∧ c.secondaryWindow ≤ c.primaryWindow + c.slack

def ThresholdTransferSchemasBudgetCertificate.budgetControlled
    (c : ThresholdTransferSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def ThresholdTransferSchemasBudgetCertificate.Ready
    (c : ThresholdTransferSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def ThresholdTransferSchemasBudgetCertificate.size
    (c : ThresholdTransferSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem thresholdTransferSchemas_budgetCertificate_le_size
    (c : ThresholdTransferSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleThresholdTransferSchemasBudgetCertificate :
    ThresholdTransferSchemasBudgetCertificate :=
  { primaryWindow := 5
    secondaryWindow := 6
    certificateBudgetWindow := 12
    slack := 1 }

example : sampleThresholdTransferSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [ThresholdTransferSchemasBudgetCertificate.controlled,
      sampleThresholdTransferSchemasBudgetCertificate]
  · norm_num [ThresholdTransferSchemasBudgetCertificate.budgetControlled,
      sampleThresholdTransferSchemasBudgetCertificate]

example :
    sampleThresholdTransferSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleThresholdTransferSchemasBudgetCertificate.size := by
  apply thresholdTransferSchemas_budgetCertificate_le_size
  constructor
  · norm_num [ThresholdTransferSchemasBudgetCertificate.controlled,
      sampleThresholdTransferSchemasBudgetCertificate]
  · norm_num [ThresholdTransferSchemasBudgetCertificate.budgetControlled,
      sampleThresholdTransferSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleThresholdTransferSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [ThresholdTransferSchemasBudgetCertificate.controlled,
      sampleThresholdTransferSchemasBudgetCertificate]
  · norm_num [ThresholdTransferSchemasBudgetCertificate.budgetControlled,
      sampleThresholdTransferSchemasBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleThresholdTransferSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleThresholdTransferSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady
    (data : List ThresholdTransferSchemasBudgetCertificate) : Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady [sampleThresholdTransferSchemasBudgetCertificate] =
      true := by
  unfold budgetCertificateListReady sampleThresholdTransferSchemasBudgetCertificate
  native_decide

end AnalyticCombinatorics.Asymptotics.ThresholdTransferSchemas
