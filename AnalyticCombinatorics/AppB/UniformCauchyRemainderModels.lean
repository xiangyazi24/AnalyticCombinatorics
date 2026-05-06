import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Uniform Cauchy remainder models.

This module records finite bookkeeping for Cauchy remainder estimates.
-/

namespace AnalyticCombinatorics.AppB.UniformCauchyRemainderModels

structure CauchyRemainderData where
  contourRadius : ℕ
  remainderWindow : ℕ
  cauchySlack : ℕ
deriving DecidableEq, Repr

def hasContourRadius (d : CauchyRemainderData) : Prop :=
  0 < d.contourRadius

def remainderWindowControlled (d : CauchyRemainderData) : Prop :=
  d.remainderWindow ≤ d.contourRadius + d.cauchySlack

def cauchyRemainderReady (d : CauchyRemainderData) : Prop :=
  hasContourRadius d ∧ remainderWindowControlled d

def cauchyRemainderBudget (d : CauchyRemainderData) : ℕ :=
  d.contourRadius + d.remainderWindow + d.cauchySlack

theorem cauchyRemainderReady.hasContourRadius {d : CauchyRemainderData}
    (h : cauchyRemainderReady d) :
    hasContourRadius d ∧ remainderWindowControlled d ∧
      d.remainderWindow ≤ cauchyRemainderBudget d := by
  refine ⟨h.1, h.2, ?_⟩
  unfold cauchyRemainderBudget
  omega

theorem remainderWindow_le_budget (d : CauchyRemainderData) :
    d.remainderWindow ≤ cauchyRemainderBudget d := by
  unfold cauchyRemainderBudget
  omega

def sampleCauchyRemainderData : CauchyRemainderData :=
  { contourRadius := 6, remainderWindow := 8, cauchySlack := 3 }

example : cauchyRemainderReady sampleCauchyRemainderData := by
  norm_num [cauchyRemainderReady, hasContourRadius]
  norm_num [remainderWindowControlled, sampleCauchyRemainderData]

example : cauchyRemainderBudget sampleCauchyRemainderData = 17 := by
  native_decide

structure UniformCauchyRemainderWindow where
  contourWindow : ℕ
  remainderWindow : ℕ
  cauchySlack : ℕ
  remainderBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def UniformCauchyRemainderWindow.remainderControlled
    (w : UniformCauchyRemainderWindow) : Prop :=
  w.remainderWindow ≤ w.contourWindow + w.cauchySlack + w.slack

def uniformCauchyRemainderWindowReady (w : UniformCauchyRemainderWindow) : Prop :=
  0 < w.contourWindow ∧ w.remainderControlled ∧
    w.remainderBudget ≤ w.contourWindow + w.remainderWindow + w.slack

def UniformCauchyRemainderWindow.certificate (w : UniformCauchyRemainderWindow) : ℕ :=
  w.contourWindow + w.remainderWindow + w.cauchySlack + w.remainderBudget + w.slack

theorem uniformCauchyRemainder_budget_le_certificate (w : UniformCauchyRemainderWindow) :
    w.remainderBudget ≤ w.certificate := by
  unfold UniformCauchyRemainderWindow.certificate
  omega

def sampleUniformCauchyRemainderWindow : UniformCauchyRemainderWindow :=
  { contourWindow := 5, remainderWindow := 7, cauchySlack := 2,
    remainderBudget := 14, slack := 2 }

example : uniformCauchyRemainderWindowReady sampleUniformCauchyRemainderWindow := by
  norm_num [uniformCauchyRemainderWindowReady,
    UniformCauchyRemainderWindow.remainderControlled, sampleUniformCauchyRemainderWindow]


structure UniformCauchyRemainderModelsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def UniformCauchyRemainderModelsBudgetCertificate.controlled
    (c : UniformCauchyRemainderModelsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def UniformCauchyRemainderModelsBudgetCertificate.budgetControlled
    (c : UniformCauchyRemainderModelsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def UniformCauchyRemainderModelsBudgetCertificate.Ready
    (c : UniformCauchyRemainderModelsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def UniformCauchyRemainderModelsBudgetCertificate.size
    (c : UniformCauchyRemainderModelsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem uniformCauchyRemainderModels_budgetCertificate_le_size
    (c : UniformCauchyRemainderModelsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleUniformCauchyRemainderModelsBudgetCertificate :
    UniformCauchyRemainderModelsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleUniformCauchyRemainderModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [UniformCauchyRemainderModelsBudgetCertificate.controlled,
      sampleUniformCauchyRemainderModelsBudgetCertificate]
  · norm_num [UniformCauchyRemainderModelsBudgetCertificate.budgetControlled,
      sampleUniformCauchyRemainderModelsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleUniformCauchyRemainderModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleUniformCauchyRemainderModelsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleUniformCauchyRemainderModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [UniformCauchyRemainderModelsBudgetCertificate.controlled,
      sampleUniformCauchyRemainderModelsBudgetCertificate]
  · norm_num [UniformCauchyRemainderModelsBudgetCertificate.budgetControlled,
      sampleUniformCauchyRemainderModelsBudgetCertificate]

example :
    sampleUniformCauchyRemainderModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleUniformCauchyRemainderModelsBudgetCertificate.size := by
  apply uniformCauchyRemainderModels_budgetCertificate_le_size
  constructor
  · norm_num [UniformCauchyRemainderModelsBudgetCertificate.controlled,
      sampleUniformCauchyRemainderModelsBudgetCertificate]
  · norm_num [UniformCauchyRemainderModelsBudgetCertificate.budgetControlled,
      sampleUniformCauchyRemainderModelsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List UniformCauchyRemainderModelsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleUniformCauchyRemainderModelsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleUniformCauchyRemainderModelsBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppB.UniformCauchyRemainderModels
