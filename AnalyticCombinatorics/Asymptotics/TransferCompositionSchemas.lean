import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Transfer composition schemas.

The finite data records outer scale, inner scale, and remainder budget
for composed transfer estimates.
-/

namespace AnalyticCombinatorics.Asymptotics.TransferCompositionSchemas

structure TransferCompositionData where
  outerScale : ℕ
  innerScale : ℕ
  remainderBudget : ℕ
deriving DecidableEq, Repr

def positiveOuterScale (d : TransferCompositionData) : Prop :=
  0 < d.outerScale

def innerScaleControlled (d : TransferCompositionData) : Prop :=
  d.innerScale ≤ d.outerScale + d.remainderBudget

def transferCompositionReady (d : TransferCompositionData) : Prop :=
  positiveOuterScale d ∧ innerScaleControlled d

def transferCompositionBudget (d : TransferCompositionData) : ℕ :=
  d.outerScale + d.innerScale + d.remainderBudget

theorem transferCompositionReady.outer {d : TransferCompositionData}
    (h : transferCompositionReady d) :
    positiveOuterScale d ∧ innerScaleControlled d ∧ d.innerScale ≤ transferCompositionBudget d := by
  refine ⟨h.1, h.2, ?_⟩
  unfold transferCompositionBudget
  omega

theorem innerScale_le_compositionBudget (d : TransferCompositionData) :
    d.innerScale ≤ transferCompositionBudget d := by
  unfold transferCompositionBudget
  omega

def sampleTransferCompositionData : TransferCompositionData :=
  { outerScale := 7, innerScale := 9, remainderBudget := 3 }

example : transferCompositionReady sampleTransferCompositionData := by
  norm_num [transferCompositionReady, positiveOuterScale]
  norm_num [innerScaleControlled, sampleTransferCompositionData]

example : transferCompositionBudget sampleTransferCompositionData = 19 := by
  native_decide

/-- Finite executable readiness audit for transfer composition data. -/
def transferCompositionDataListReady
    (data : List TransferCompositionData) : Bool :=
  data.all fun d =>
    0 < d.outerScale && d.innerScale ≤ d.outerScale + d.remainderBudget

theorem transferCompositionDataList_readyWindow :
    transferCompositionDataListReady
      [{ outerScale := 4, innerScale := 5, remainderBudget := 1 },
       { outerScale := 7, innerScale := 9, remainderBudget := 3 }] = true := by
  unfold transferCompositionDataListReady
  native_decide

structure TransferCompositionWindow where
  outerWindow : ℕ
  innerWindow : ℕ
  remainderWindow : ℕ
  compositionBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def TransferCompositionWindow.innerControlled
    (w : TransferCompositionWindow) : Prop :=
  w.innerWindow ≤ w.outerWindow + w.remainderWindow + w.slack

def transferCompositionWindowReady (w : TransferCompositionWindow) : Prop :=
  0 < w.outerWindow ∧ w.innerControlled ∧
    w.compositionBudget ≤ w.outerWindow + w.innerWindow + w.remainderWindow + w.slack

def TransferCompositionWindow.certificate (w : TransferCompositionWindow) : ℕ :=
  w.outerWindow + w.innerWindow + w.remainderWindow + w.compositionBudget + w.slack

theorem transferComposition_budget_le_certificate
    (w : TransferCompositionWindow) :
    w.compositionBudget ≤ w.certificate := by
  unfold TransferCompositionWindow.certificate
  omega

def sampleTransferCompositionWindow : TransferCompositionWindow :=
  { outerWindow := 7, innerWindow := 9, remainderWindow := 3,
    compositionBudget := 20, slack := 1 }

example : transferCompositionWindowReady sampleTransferCompositionWindow := by
  norm_num [transferCompositionWindowReady,
    TransferCompositionWindow.innerControlled, sampleTransferCompositionWindow]

/-- A refinement certificate for transfer composition windows. -/
structure TransferCompositionCertificate where
  outerWindow : ℕ
  innerWindow : ℕ
  remainderWindow : ℕ
  compositionWindow : ℕ
  slack : ℕ

/-- The inner and composition windows are controlled by the outer scale. -/
def transferCompositionCertificateControlled
    (w : TransferCompositionCertificate) : Prop :=
  0 < w.outerWindow ∧
    w.innerWindow ≤ w.outerWindow + w.remainderWindow + w.slack ∧
      w.compositionWindow ≤ w.outerWindow + w.innerWindow + w.remainderWindow + w.slack

/-- Readiness for a transfer composition certificate. -/
def transferCompositionCertificateReady
    (w : TransferCompositionCertificate) : Prop :=
  transferCompositionCertificateControlled w ∧
    w.compositionWindow ≤
      w.outerWindow + w.innerWindow + w.remainderWindow + w.compositionWindow + w.slack

/-- Total size of a transfer composition certificate. -/
def transferCompositionCertificateSize
    (w : TransferCompositionCertificate) : ℕ :=
  w.outerWindow + w.innerWindow + w.remainderWindow + w.compositionWindow + w.slack

theorem transferCompositionCertificate_composition_le_size
    (w : TransferCompositionCertificate)
    (h : transferCompositionCertificateReady w) :
    w.compositionWindow ≤ transferCompositionCertificateSize w := by
  rcases h with ⟨_, hbudget⟩
  unfold transferCompositionCertificateSize
  omega

def sampleTransferCompositionCertificate :
    TransferCompositionCertificate where
  outerWindow := 7
  innerWindow := 9
  remainderWindow := 3
  compositionWindow := 20
  slack := 1

example :
    transferCompositionCertificateReady sampleTransferCompositionCertificate := by
  norm_num [transferCompositionCertificateReady,
    transferCompositionCertificateControlled, sampleTransferCompositionCertificate]

example :
    sampleTransferCompositionCertificate.compositionWindow ≤
      transferCompositionCertificateSize sampleTransferCompositionCertificate := by
  apply transferCompositionCertificate_composition_le_size
  norm_num [transferCompositionCertificateReady,
    transferCompositionCertificateControlled, sampleTransferCompositionCertificate]

/-- A refinement certificate with the transfer-composition budget separated from size. -/
structure TransferCompositionRefinementCertificate where
  outerWindow : ℕ
  innerWindow : ℕ
  remainderWindow : ℕ
  compositionWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def TransferCompositionRefinementCertificate.compositionControlled
    (cert : TransferCompositionRefinementCertificate) : Prop :=
  0 < cert.outerWindow ∧
    cert.innerWindow ≤ cert.outerWindow + cert.remainderWindow + cert.slack ∧
      cert.compositionWindow ≤
        cert.outerWindow + cert.innerWindow + cert.remainderWindow + cert.slack

def TransferCompositionRefinementCertificate.budgetControlled
    (cert : TransferCompositionRefinementCertificate) : Prop :=
  cert.certificateBudgetWindow ≤
    cert.outerWindow + cert.innerWindow + cert.remainderWindow +
      cert.compositionWindow + cert.slack

def transferCompositionRefinementReady
    (cert : TransferCompositionRefinementCertificate) : Prop :=
  cert.compositionControlled ∧ cert.budgetControlled

def TransferCompositionRefinementCertificate.size
    (cert : TransferCompositionRefinementCertificate) : ℕ :=
  cert.outerWindow + cert.innerWindow + cert.remainderWindow +
    cert.compositionWindow + cert.slack

theorem transferComposition_certificateBudgetWindow_le_size
    (cert : TransferCompositionRefinementCertificate)
    (h : transferCompositionRefinementReady cert) :
    cert.certificateBudgetWindow ≤ cert.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleTransferCompositionRefinementCertificate :
    TransferCompositionRefinementCertificate :=
  { outerWindow := 7, innerWindow := 9, remainderWindow := 3,
    compositionWindow := 20, certificateBudgetWindow := 40, slack := 1 }

example :
    transferCompositionRefinementReady
      sampleTransferCompositionRefinementCertificate := by
  norm_num [transferCompositionRefinementReady,
    TransferCompositionRefinementCertificate.compositionControlled,
    TransferCompositionRefinementCertificate.budgetControlled,
    sampleTransferCompositionRefinementCertificate]

example :
    sampleTransferCompositionRefinementCertificate.certificateBudgetWindow ≤
      sampleTransferCompositionRefinementCertificate.size := by
  apply transferComposition_certificateBudgetWindow_le_size
  norm_num [transferCompositionRefinementReady,
    TransferCompositionRefinementCertificate.compositionControlled,
    TransferCompositionRefinementCertificate.budgetControlled,
    sampleTransferCompositionRefinementCertificate]


structure TransferCompositionSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def TransferCompositionSchemasBudgetCertificate.controlled
    (c : TransferCompositionSchemasBudgetCertificate) : Prop :=
  0 < c.primaryWindow ∧ c.secondaryWindow ≤ c.primaryWindow + c.slack

def TransferCompositionSchemasBudgetCertificate.budgetControlled
    (c : TransferCompositionSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def TransferCompositionSchemasBudgetCertificate.Ready
    (c : TransferCompositionSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def TransferCompositionSchemasBudgetCertificate.size
    (c : TransferCompositionSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem transferCompositionSchemas_budgetCertificate_le_size
    (c : TransferCompositionSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleTransferCompositionSchemasBudgetCertificate :
    TransferCompositionSchemasBudgetCertificate :=
  { primaryWindow := 5
    secondaryWindow := 6
    certificateBudgetWindow := 12
    slack := 1 }

example : sampleTransferCompositionSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [TransferCompositionSchemasBudgetCertificate.controlled,
      sampleTransferCompositionSchemasBudgetCertificate]
  · norm_num [TransferCompositionSchemasBudgetCertificate.budgetControlled,
      sampleTransferCompositionSchemasBudgetCertificate]

example :
    sampleTransferCompositionSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleTransferCompositionSchemasBudgetCertificate.size := by
  apply transferCompositionSchemas_budgetCertificate_le_size
  constructor
  · norm_num [TransferCompositionSchemasBudgetCertificate.controlled,
      sampleTransferCompositionSchemasBudgetCertificate]
  · norm_num [TransferCompositionSchemasBudgetCertificate.budgetControlled,
      sampleTransferCompositionSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleTransferCompositionSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [TransferCompositionSchemasBudgetCertificate.controlled,
      sampleTransferCompositionSchemasBudgetCertificate]
  · norm_num [TransferCompositionSchemasBudgetCertificate.budgetControlled,
      sampleTransferCompositionSchemasBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleTransferCompositionSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleTransferCompositionSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady
    (data : List TransferCompositionSchemasBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleTransferCompositionSchemasBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleTransferCompositionSchemasBudgetCertificate
  native_decide
end AnalyticCombinatorics.Asymptotics.TransferCompositionSchemas
