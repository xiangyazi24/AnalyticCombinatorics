import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Martingale tightness schemas.

The finite record stores filtration depth, increment budget, and
tightness slack.
-/

namespace AnalyticCombinatorics.AppC.MartingaleTightnessSchemas

structure MartingaleTightnessData where
  filtrationDepth : ℕ
  incrementBudget : ℕ
  tightnessSlack : ℕ
deriving DecidableEq, Repr

def filtrationDepthPositive (d : MartingaleTightnessData) : Prop :=
  0 < d.filtrationDepth

def incrementsControlled (d : MartingaleTightnessData) : Prop :=
  d.incrementBudget ≤ d.filtrationDepth + d.tightnessSlack

def martingaleTightnessReady (d : MartingaleTightnessData) : Prop :=
  filtrationDepthPositive d ∧ incrementsControlled d

def martingaleTightnessBudget (d : MartingaleTightnessData) : ℕ :=
  d.filtrationDepth + d.incrementBudget + d.tightnessSlack

theorem martingaleTightnessReady.depth {d : MartingaleTightnessData}
    (h : martingaleTightnessReady d) :
    filtrationDepthPositive d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem incrementBudget_le_martingaleBudget
    (d : MartingaleTightnessData) :
    d.incrementBudget ≤ martingaleTightnessBudget d := by
  unfold martingaleTightnessBudget
  omega

def sampleMartingaleTightnessData : MartingaleTightnessData :=
  { filtrationDepth := 6, incrementBudget := 8, tightnessSlack := 3 }

example : martingaleTightnessReady sampleMartingaleTightnessData := by
  norm_num [martingaleTightnessReady, filtrationDepthPositive]
  norm_num [incrementsControlled, sampleMartingaleTightnessData]

example : martingaleTightnessBudget sampleMartingaleTightnessData = 17 := by
  native_decide

structure MartingaleTightnessWindow where
  depthWindow : ℕ
  incrementWindow : ℕ
  tightnessSlack : ℕ
  tightnessBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def MartingaleTightnessWindow.incrementsControlled
    (w : MartingaleTightnessWindow) : Prop :=
  w.incrementWindow ≤ w.depthWindow + w.tightnessSlack + w.slack

def martingaleTightnessWindowReady (w : MartingaleTightnessWindow) : Prop :=
  0 < w.depthWindow ∧ w.incrementsControlled ∧
    w.tightnessBudget ≤ w.depthWindow + w.incrementWindow + w.slack

def MartingaleTightnessWindow.certificate (w : MartingaleTightnessWindow) : ℕ :=
  w.depthWindow + w.incrementWindow + w.tightnessSlack + w.tightnessBudget + w.slack

theorem martingaleTightness_tightnessBudget_le_certificate
    (w : MartingaleTightnessWindow) :
    w.tightnessBudget ≤ w.certificate := by
  unfold MartingaleTightnessWindow.certificate
  omega

def sampleMartingaleTightnessWindow : MartingaleTightnessWindow :=
  { depthWindow := 5, incrementWindow := 7, tightnessSlack := 2,
    tightnessBudget := 14, slack := 2 }

example : martingaleTightnessWindowReady sampleMartingaleTightnessWindow := by
  norm_num [martingaleTightnessWindowReady,
    MartingaleTightnessWindow.incrementsControlled, sampleMartingaleTightnessWindow]


structure MartingaleTightnessSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def MartingaleTightnessSchemasBudgetCertificate.controlled
    (c : MartingaleTightnessSchemasBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def MartingaleTightnessSchemasBudgetCertificate.budgetControlled
    (c : MartingaleTightnessSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def MartingaleTightnessSchemasBudgetCertificate.Ready
    (c : MartingaleTightnessSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def MartingaleTightnessSchemasBudgetCertificate.size
    (c : MartingaleTightnessSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem martingaleTightnessSchemas_budgetCertificate_le_size
    (c : MartingaleTightnessSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleMartingaleTightnessSchemasBudgetCertificate :
    MartingaleTightnessSchemasBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleMartingaleTightnessSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [MartingaleTightnessSchemasBudgetCertificate.controlled,
      sampleMartingaleTightnessSchemasBudgetCertificate]
  · norm_num [MartingaleTightnessSchemasBudgetCertificate.budgetControlled,
      sampleMartingaleTightnessSchemasBudgetCertificate]

example : sampleMartingaleTightnessSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [MartingaleTightnessSchemasBudgetCertificate.controlled,
      sampleMartingaleTightnessSchemasBudgetCertificate]
  · norm_num [MartingaleTightnessSchemasBudgetCertificate.budgetControlled,
      sampleMartingaleTightnessSchemasBudgetCertificate]

example :
    sampleMartingaleTightnessSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleMartingaleTightnessSchemasBudgetCertificate.size := by
  apply martingaleTightnessSchemas_budgetCertificate_le_size
  constructor
  · norm_num [MartingaleTightnessSchemasBudgetCertificate.controlled,
      sampleMartingaleTightnessSchemasBudgetCertificate]
  · norm_num [MartingaleTightnessSchemasBudgetCertificate.budgetControlled,
      sampleMartingaleTightnessSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_le_size :
    sampleMartingaleTightnessSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleMartingaleTightnessSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List MartingaleTightnessSchemasBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleMartingaleTightnessSchemasBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleMartingaleTightnessSchemasBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppC.MartingaleTightnessSchemas
