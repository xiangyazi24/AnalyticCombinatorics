import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Finite label transfer models.

The finite record stores source labels, target labels, and relabelling
slack.
-/

namespace AnalyticCombinatorics.AppA.FiniteLabelTransferModels

structure LabelTransferData where
  sourceLabels : ℕ
  targetLabels : ℕ
  relabelSlack : ℕ
deriving DecidableEq, Repr

def sourceLabelsPositive (d : LabelTransferData) : Prop :=
  0 < d.sourceLabels

def targetLabelsControlled (d : LabelTransferData) : Prop :=
  d.targetLabels ≤ d.sourceLabels + d.relabelSlack

def labelTransferReady (d : LabelTransferData) : Prop :=
  sourceLabelsPositive d ∧ targetLabelsControlled d

def labelTransferBudget (d : LabelTransferData) : ℕ :=
  d.sourceLabels + d.targetLabels + d.relabelSlack

theorem labelTransferReady.source {d : LabelTransferData}
    (h : labelTransferReady d) :
    sourceLabelsPositive d ∧ targetLabelsControlled d ∧ d.targetLabels ≤ labelTransferBudget d := by
  refine ⟨h.1, h.2, ?_⟩
  unfold labelTransferBudget
  omega

theorem targetLabels_le_labelTransferBudget (d : LabelTransferData) :
    d.targetLabels ≤ labelTransferBudget d := by
  unfold labelTransferBudget
  omega

def sampleLabelTransferData : LabelTransferData :=
  { sourceLabels := 7, targetLabels := 9, relabelSlack := 3 }

example : labelTransferReady sampleLabelTransferData := by
  norm_num [labelTransferReady, sourceLabelsPositive]
  norm_num [targetLabelsControlled, sampleLabelTransferData]

example : labelTransferBudget sampleLabelTransferData = 19 := by
  native_decide

structure LabelTransferWindow where
  sourceLabels : ℕ
  targetLabels : ℕ
  relabelSlack : ℕ
  transportBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def LabelTransferWindow.targetControlled (w : LabelTransferWindow) : Prop :=
  w.targetLabels ≤ w.sourceLabels + w.relabelSlack + w.slack

def LabelTransferWindow.transportControlled (w : LabelTransferWindow) : Prop :=
  w.transportBudget ≤ w.sourceLabels + w.targetLabels + w.relabelSlack + w.slack

def labelTransferWindowReady (w : LabelTransferWindow) : Prop :=
  0 < w.sourceLabels ∧
    w.targetControlled ∧
    w.transportControlled

def LabelTransferWindow.certificate (w : LabelTransferWindow) : ℕ :=
  w.sourceLabels + w.targetLabels + w.relabelSlack + w.slack

theorem labelTransfer_transportBudget_le_certificate {w : LabelTransferWindow}
    (h : labelTransferWindowReady w) :
    w.transportBudget ≤ w.certificate := by
  rcases h with ⟨_, _, htransport⟩
  exact htransport

def sampleLabelTransferWindow : LabelTransferWindow :=
  { sourceLabels := 7, targetLabels := 9, relabelSlack := 3, transportBudget := 18, slack := 0 }

example : labelTransferWindowReady sampleLabelTransferWindow := by
  norm_num [labelTransferWindowReady, LabelTransferWindow.targetControlled,
    LabelTransferWindow.transportControlled, sampleLabelTransferWindow]

example : sampleLabelTransferWindow.certificate = 19 := by
  native_decide


structure FiniteLabelTransferModelsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def FiniteLabelTransferModelsBudgetCertificate.controlled
    (c : FiniteLabelTransferModelsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def FiniteLabelTransferModelsBudgetCertificate.budgetControlled
    (c : FiniteLabelTransferModelsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def FiniteLabelTransferModelsBudgetCertificate.Ready
    (c : FiniteLabelTransferModelsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def FiniteLabelTransferModelsBudgetCertificate.size
    (c : FiniteLabelTransferModelsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem finiteLabelTransferModels_budgetCertificate_le_size
    (c : FiniteLabelTransferModelsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleFiniteLabelTransferModelsBudgetCertificate :
    FiniteLabelTransferModelsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleFiniteLabelTransferModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [FiniteLabelTransferModelsBudgetCertificate.controlled,
      sampleFiniteLabelTransferModelsBudgetCertificate]
  · norm_num [FiniteLabelTransferModelsBudgetCertificate.budgetControlled,
      sampleFiniteLabelTransferModelsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleFiniteLabelTransferModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleFiniteLabelTransferModelsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleFiniteLabelTransferModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [FiniteLabelTransferModelsBudgetCertificate.controlled,
      sampleFiniteLabelTransferModelsBudgetCertificate]
  · norm_num [FiniteLabelTransferModelsBudgetCertificate.budgetControlled,
      sampleFiniteLabelTransferModelsBudgetCertificate]

example :
    sampleFiniteLabelTransferModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleFiniteLabelTransferModelsBudgetCertificate.size := by
  apply finiteLabelTransferModels_budgetCertificate_le_size
  constructor
  · norm_num [FiniteLabelTransferModelsBudgetCertificate.controlled,
      sampleFiniteLabelTransferModelsBudgetCertificate]
  · norm_num [FiniteLabelTransferModelsBudgetCertificate.budgetControlled,
      sampleFiniteLabelTransferModelsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List FiniteLabelTransferModelsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleFiniteLabelTransferModelsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleFiniteLabelTransferModelsBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppA.FiniteLabelTransferModels
