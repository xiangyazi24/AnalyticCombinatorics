import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Hayman window schemas.

This module records finite bookkeeping for Hayman-admissible windows: a
positive admissible radius controls variance scale with saddle slack.
-/

namespace AnalyticCombinatorics.PartB.Ch8.HaymanWindowSchemas

structure HaymanWindowData where
  admissibleRadius : ℕ
  varianceScale : ℕ
  saddleSlack : ℕ
deriving DecidableEq, Repr

def hasAdmissibleRadius (d : HaymanWindowData) : Prop :=
  0 < d.admissibleRadius

def varianceScaleControlled (d : HaymanWindowData) : Prop :=
  d.varianceScale ≤ d.admissibleRadius + d.saddleSlack

def haymanWindowReady (d : HaymanWindowData) : Prop :=
  hasAdmissibleRadius d ∧ varianceScaleControlled d

def haymanWindowBudget (d : HaymanWindowData) : ℕ :=
  d.admissibleRadius + d.varianceScale + d.saddleSlack

theorem haymanWindowReady.hasAdmissibleRadius {d : HaymanWindowData}
    (h : haymanWindowReady d) :
    hasAdmissibleRadius d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem varianceScale_le_budget (d : HaymanWindowData) :
    d.varianceScale ≤ haymanWindowBudget d := by
  unfold haymanWindowBudget
  omega

def sampleHaymanWindowData : HaymanWindowData :=
  { admissibleRadius := 6, varianceScale := 8, saddleSlack := 3 }

example : haymanWindowReady sampleHaymanWindowData := by
  norm_num [haymanWindowReady, hasAdmissibleRadius]
  norm_num [varianceScaleControlled, sampleHaymanWindowData]

example : haymanWindowBudget sampleHaymanWindowData = 17 := by
  native_decide

structure HaymanWindowBudgetCertificate where
  admissibleRadiusWindow : ℕ
  varianceScaleWindow : ℕ
  saddleSlackWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def HaymanWindowBudgetCertificate.controlled
    (c : HaymanWindowBudgetCertificate) : Prop :=
  0 < c.admissibleRadiusWindow ∧
    c.varianceScaleWindow ≤ c.admissibleRadiusWindow + c.saddleSlackWindow + c.slack

def HaymanWindowBudgetCertificate.budgetControlled
    (c : HaymanWindowBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.admissibleRadiusWindow + c.varianceScaleWindow + c.saddleSlackWindow + c.slack

def HaymanWindowBudgetCertificate.Ready
    (c : HaymanWindowBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def HaymanWindowBudgetCertificate.size
    (c : HaymanWindowBudgetCertificate) : ℕ :=
  c.admissibleRadiusWindow + c.varianceScaleWindow + c.saddleSlackWindow + c.slack

theorem haymanWindow_budgetCertificate_le_size
    (c : HaymanWindowBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleHaymanWindowBudgetCertificate :
    HaymanWindowBudgetCertificate :=
  { admissibleRadiusWindow := 6
    varianceScaleWindow := 8
    saddleSlackWindow := 3
    certificateBudgetWindow := 18
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleHaymanWindowBudgetCertificate.Ready := by
  constructor
  · norm_num [HaymanWindowBudgetCertificate.controlled,
      sampleHaymanWindowBudgetCertificate]
  · norm_num [HaymanWindowBudgetCertificate.budgetControlled,
      sampleHaymanWindowBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleHaymanWindowBudgetCertificate.certificateBudgetWindow ≤
      sampleHaymanWindowBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleHaymanWindowBudgetCertificate.Ready := by
  constructor
  · norm_num [HaymanWindowBudgetCertificate.controlled,
      sampleHaymanWindowBudgetCertificate]
  · norm_num [HaymanWindowBudgetCertificate.budgetControlled,
      sampleHaymanWindowBudgetCertificate]

example :
    sampleHaymanWindowBudgetCertificate.certificateBudgetWindow ≤
      sampleHaymanWindowBudgetCertificate.size := by
  apply haymanWindow_budgetCertificate_le_size
  constructor
  · norm_num [HaymanWindowBudgetCertificate.controlled,
      sampleHaymanWindowBudgetCertificate]
  · norm_num [HaymanWindowBudgetCertificate.budgetControlled,
      sampleHaymanWindowBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List HaymanWindowBudgetCertificate) : Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady [sampleHaymanWindowBudgetCertificate] = true := by
  unfold budgetCertificateListReady sampleHaymanWindowBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch8.HaymanWindowSchemas
