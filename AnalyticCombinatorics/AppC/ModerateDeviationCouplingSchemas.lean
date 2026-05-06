import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Moderate deviation coupling schemas.

This module records finite bookkeeping for moderate deviation couplings.
-/

namespace AnalyticCombinatorics.AppC.ModerateDeviationCouplingSchemas

structure ModerateDeviationCouplingData where
  deviationScale : ℕ
  couplingWindow : ℕ
  deviationSlack : ℕ
deriving DecidableEq, Repr

def hasDeviationScale (d : ModerateDeviationCouplingData) : Prop :=
  0 < d.deviationScale

def couplingWindowControlled (d : ModerateDeviationCouplingData) : Prop :=
  d.couplingWindow ≤ d.deviationScale + d.deviationSlack

def moderateDeviationCouplingReady
    (d : ModerateDeviationCouplingData) : Prop :=
  hasDeviationScale d ∧ couplingWindowControlled d

def moderateDeviationCouplingBudget
    (d : ModerateDeviationCouplingData) : ℕ :=
  d.deviationScale + d.couplingWindow + d.deviationSlack

theorem moderateDeviationCouplingReady.hasDeviationScale
    {d : ModerateDeviationCouplingData}
    (h : moderateDeviationCouplingReady d) :
    hasDeviationScale d ∧ couplingWindowControlled d ∧
      d.couplingWindow ≤ moderateDeviationCouplingBudget d := by
  refine ⟨h.1, h.2, ?_⟩
  unfold moderateDeviationCouplingBudget
  omega

theorem couplingWindow_le_budget (d : ModerateDeviationCouplingData) :
    d.couplingWindow ≤ moderateDeviationCouplingBudget d := by
  unfold moderateDeviationCouplingBudget
  omega

def sampleModerateDeviationCouplingData : ModerateDeviationCouplingData :=
  { deviationScale := 6, couplingWindow := 8, deviationSlack := 3 }

example : moderateDeviationCouplingReady
    sampleModerateDeviationCouplingData := by
  norm_num [moderateDeviationCouplingReady, hasDeviationScale]
  norm_num [couplingWindowControlled, sampleModerateDeviationCouplingData]

example :
    moderateDeviationCouplingBudget sampleModerateDeviationCouplingData = 17 := by
  native_decide

structure ModerateDeviationCouplingWindow where
  deviationWindow : ℕ
  couplingWindow : ℕ
  deviationSlack : ℕ
  couplingBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def ModerateDeviationCouplingWindow.couplingControlled
    (w : ModerateDeviationCouplingWindow) : Prop :=
  w.couplingWindow ≤ w.deviationWindow + w.deviationSlack + w.slack

def moderateDeviationCouplingWindowReady
    (w : ModerateDeviationCouplingWindow) : Prop :=
  0 < w.deviationWindow ∧ w.couplingControlled ∧
    w.couplingBudget ≤ w.deviationWindow + w.couplingWindow + w.slack

def ModerateDeviationCouplingWindow.certificate
    (w : ModerateDeviationCouplingWindow) : ℕ :=
  w.deviationWindow + w.couplingWindow + w.deviationSlack + w.couplingBudget + w.slack

theorem moderateDeviationCoupling_couplingBudget_le_certificate
    (w : ModerateDeviationCouplingWindow) :
    w.couplingBudget ≤ w.certificate := by
  unfold ModerateDeviationCouplingWindow.certificate
  omega

def sampleModerateDeviationCouplingWindow : ModerateDeviationCouplingWindow :=
  { deviationWindow := 5, couplingWindow := 7, deviationSlack := 2,
    couplingBudget := 14, slack := 2 }

example : moderateDeviationCouplingWindowReady
    sampleModerateDeviationCouplingWindow := by
  norm_num [moderateDeviationCouplingWindowReady,
    ModerateDeviationCouplingWindow.couplingControlled, sampleModerateDeviationCouplingWindow]


structure ModerateDeviationCouplingSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def ModerateDeviationCouplingSchemasBudgetCertificate.controlled
    (c : ModerateDeviationCouplingSchemasBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def ModerateDeviationCouplingSchemasBudgetCertificate.budgetControlled
    (c : ModerateDeviationCouplingSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def ModerateDeviationCouplingSchemasBudgetCertificate.Ready
    (c : ModerateDeviationCouplingSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def ModerateDeviationCouplingSchemasBudgetCertificate.size
    (c : ModerateDeviationCouplingSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem moderateDeviationCouplingSchemas_budgetCertificate_le_size
    (c : ModerateDeviationCouplingSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleModerateDeviationCouplingSchemasBudgetCertificate :
    ModerateDeviationCouplingSchemasBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleModerateDeviationCouplingSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [ModerateDeviationCouplingSchemasBudgetCertificate.controlled,
      sampleModerateDeviationCouplingSchemasBudgetCertificate]
  · norm_num [ModerateDeviationCouplingSchemasBudgetCertificate.budgetControlled,
      sampleModerateDeviationCouplingSchemasBudgetCertificate]

example : sampleModerateDeviationCouplingSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [ModerateDeviationCouplingSchemasBudgetCertificate.controlled,
      sampleModerateDeviationCouplingSchemasBudgetCertificate]
  · norm_num [ModerateDeviationCouplingSchemasBudgetCertificate.budgetControlled,
      sampleModerateDeviationCouplingSchemasBudgetCertificate]

example :
    sampleModerateDeviationCouplingSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleModerateDeviationCouplingSchemasBudgetCertificate.size := by
  apply moderateDeviationCouplingSchemas_budgetCertificate_le_size
  constructor
  · norm_num [ModerateDeviationCouplingSchemasBudgetCertificate.controlled,
      sampleModerateDeviationCouplingSchemasBudgetCertificate]
  · norm_num [ModerateDeviationCouplingSchemasBudgetCertificate.budgetControlled,
      sampleModerateDeviationCouplingSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_le_size :
    sampleModerateDeviationCouplingSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleModerateDeviationCouplingSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady
    (data : List ModerateDeviationCouplingSchemasBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleModerateDeviationCouplingSchemasBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleModerateDeviationCouplingSchemasBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppC.ModerateDeviationCouplingSchemas
