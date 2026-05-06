import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Moderate deviation schemas.

The finite schema records deviation scale, variance scale, and tail slack
for moderate deviation estimates.
-/

namespace AnalyticCombinatorics.AppC.ModerateDeviationSchemas

structure ModerateDeviationData where
  deviationScale : ℕ
  varianceScale : ℕ
  tailSlack : ℕ
deriving DecidableEq, Repr

def varianceScalePositive (d : ModerateDeviationData) : Prop :=
  0 < d.varianceScale

def deviationControlled (d : ModerateDeviationData) : Prop :=
  d.deviationScale ≤ d.varianceScale + d.tailSlack

def moderateDeviationReady (d : ModerateDeviationData) : Prop :=
  varianceScalePositive d ∧ deviationControlled d

def moderateDeviationBudget (d : ModerateDeviationData) : ℕ :=
  d.deviationScale + d.varianceScale + d.tailSlack

theorem moderateDeviationReady.variance {d : ModerateDeviationData}
    (h : moderateDeviationReady d) :
    varianceScalePositive d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem deviationScale_le_moderateDeviationBudget
    (d : ModerateDeviationData) :
    d.deviationScale ≤ moderateDeviationBudget d := by
  unfold moderateDeviationBudget
  omega

def sampleModerateDeviationData : ModerateDeviationData :=
  { deviationScale := 7, varianceScale := 5, tailSlack := 3 }

example : moderateDeviationReady sampleModerateDeviationData := by
  norm_num [moderateDeviationReady, varianceScalePositive]
  norm_num [deviationControlled, sampleModerateDeviationData]

example : moderateDeviationBudget sampleModerateDeviationData = 15 := by
  native_decide

structure ModerateDeviationWindow where
  deviationWindow : ℕ
  varianceWindow : ℕ
  tailSlack : ℕ
  deviationBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def ModerateDeviationWindow.deviationControlled (w : ModerateDeviationWindow) : Prop :=
  w.deviationWindow ≤ w.varianceWindow + w.tailSlack + w.slack

def moderateDeviationWindowReady (w : ModerateDeviationWindow) : Prop :=
  0 < w.varianceWindow ∧ w.deviationControlled ∧
    w.deviationBudget ≤ w.deviationWindow + w.varianceWindow + w.slack

def ModerateDeviationWindow.certificate (w : ModerateDeviationWindow) : ℕ :=
  w.deviationWindow + w.varianceWindow + w.tailSlack + w.deviationBudget + w.slack

theorem moderateDeviation_deviationBudget_le_certificate
    (w : ModerateDeviationWindow) :
    w.deviationBudget ≤ w.certificate := by
  unfold ModerateDeviationWindow.certificate
  omega

def sampleModerateDeviationWindow : ModerateDeviationWindow :=
  { deviationWindow := 6, varianceWindow := 5, tailSlack := 2, deviationBudget := 12, slack := 1 }

example : moderateDeviationWindowReady sampleModerateDeviationWindow := by
  norm_num [moderateDeviationWindowReady, ModerateDeviationWindow.deviationControlled,
    sampleModerateDeviationWindow]


structure ModerateDeviationSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def ModerateDeviationSchemasBudgetCertificate.controlled
    (c : ModerateDeviationSchemasBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def ModerateDeviationSchemasBudgetCertificate.budgetControlled
    (c : ModerateDeviationSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def ModerateDeviationSchemasBudgetCertificate.Ready
    (c : ModerateDeviationSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def ModerateDeviationSchemasBudgetCertificate.size
    (c : ModerateDeviationSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem moderateDeviationSchemas_budgetCertificate_le_size
    (c : ModerateDeviationSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleModerateDeviationSchemasBudgetCertificate :
    ModerateDeviationSchemasBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleModerateDeviationSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [ModerateDeviationSchemasBudgetCertificate.controlled,
      sampleModerateDeviationSchemasBudgetCertificate]
  · norm_num [ModerateDeviationSchemasBudgetCertificate.budgetControlled,
      sampleModerateDeviationSchemasBudgetCertificate]

example : sampleModerateDeviationSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [ModerateDeviationSchemasBudgetCertificate.controlled,
      sampleModerateDeviationSchemasBudgetCertificate]
  · norm_num [ModerateDeviationSchemasBudgetCertificate.budgetControlled,
      sampleModerateDeviationSchemasBudgetCertificate]

example :
    sampleModerateDeviationSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleModerateDeviationSchemasBudgetCertificate.size := by
  apply moderateDeviationSchemas_budgetCertificate_le_size
  constructor
  · norm_num [ModerateDeviationSchemasBudgetCertificate.controlled,
      sampleModerateDeviationSchemasBudgetCertificate]
  · norm_num [ModerateDeviationSchemasBudgetCertificate.budgetControlled,
      sampleModerateDeviationSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_le_size :
    sampleModerateDeviationSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleModerateDeviationSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List ModerateDeviationSchemasBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleModerateDeviationSchemasBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleModerateDeviationSchemasBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppC.ModerateDeviationSchemas
