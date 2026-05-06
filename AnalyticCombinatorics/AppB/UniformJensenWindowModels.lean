import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Uniform Jensen window models.

This module records finite bookkeeping for Jensen formula windows.
-/

namespace AnalyticCombinatorics.AppB.UniformJensenWindowModels

structure JensenWindowData where
  zeroCount : ℕ
  radiusWindow : ℕ
  jensenSlack : ℕ
deriving DecidableEq, Repr

def hasZeroCount (d : JensenWindowData) : Prop :=
  0 < d.zeroCount

def radiusWindowControlled (d : JensenWindowData) : Prop :=
  d.radiusWindow ≤ d.zeroCount + d.jensenSlack

def jensenWindowReady (d : JensenWindowData) : Prop :=
  hasZeroCount d ∧ radiusWindowControlled d

def jensenWindowBudget (d : JensenWindowData) : ℕ :=
  d.zeroCount + d.radiusWindow + d.jensenSlack

theorem jensenWindowReady.hasZeroCount {d : JensenWindowData}
    (h : jensenWindowReady d) :
    hasZeroCount d ∧ radiusWindowControlled d ∧
      d.radiusWindow ≤ jensenWindowBudget d := by
  refine ⟨h.1, h.2, ?_⟩
  unfold jensenWindowBudget
  omega

theorem radiusWindow_le_budget (d : JensenWindowData) :
    d.radiusWindow ≤ jensenWindowBudget d := by
  unfold jensenWindowBudget
  omega

def sampleJensenWindowData : JensenWindowData :=
  { zeroCount := 6, radiusWindow := 8, jensenSlack := 3 }

example : jensenWindowReady sampleJensenWindowData := by
  norm_num [jensenWindowReady, hasZeroCount]
  norm_num [radiusWindowControlled, sampleJensenWindowData]

example : jensenWindowBudget sampleJensenWindowData = 17 := by
  native_decide

structure UniformJensenWindow where
  zeroWindow : ℕ
  radiusWindow : ℕ
  jensenSlack : ℕ
  radiusBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def UniformJensenWindow.radiusControlled (w : UniformJensenWindow) : Prop :=
  w.radiusWindow ≤ w.zeroWindow + w.jensenSlack + w.slack

def uniformJensenWindowReady (w : UniformJensenWindow) : Prop :=
  0 < w.zeroWindow ∧ w.radiusControlled ∧
    w.radiusBudget ≤ w.zeroWindow + w.radiusWindow + w.slack

def UniformJensenWindow.certificate (w : UniformJensenWindow) : ℕ :=
  w.zeroWindow + w.radiusWindow + w.jensenSlack + w.radiusBudget + w.slack

theorem uniformJensen_radiusBudget_le_certificate (w : UniformJensenWindow) :
    w.radiusBudget ≤ w.certificate := by
  unfold UniformJensenWindow.certificate
  omega

def sampleUniformJensenWindow : UniformJensenWindow :=
  { zeroWindow := 5, radiusWindow := 7, jensenSlack := 2, radiusBudget := 14, slack := 2 }

example : uniformJensenWindowReady sampleUniformJensenWindow := by
  norm_num [uniformJensenWindowReady, UniformJensenWindow.radiusControlled,
    sampleUniformJensenWindow]


structure UniformJensenWindowModelsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def UniformJensenWindowModelsBudgetCertificate.controlled
    (c : UniformJensenWindowModelsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def UniformJensenWindowModelsBudgetCertificate.budgetControlled
    (c : UniformJensenWindowModelsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def UniformJensenWindowModelsBudgetCertificate.Ready
    (c : UniformJensenWindowModelsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def UniformJensenWindowModelsBudgetCertificate.size
    (c : UniformJensenWindowModelsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem uniformJensenWindowModels_budgetCertificate_le_size
    (c : UniformJensenWindowModelsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleUniformJensenWindowModelsBudgetCertificate :
    UniformJensenWindowModelsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleUniformJensenWindowModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [UniformJensenWindowModelsBudgetCertificate.controlled,
      sampleUniformJensenWindowModelsBudgetCertificate]
  · norm_num [UniformJensenWindowModelsBudgetCertificate.budgetControlled,
      sampleUniformJensenWindowModelsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleUniformJensenWindowModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleUniformJensenWindowModelsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleUniformJensenWindowModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [UniformJensenWindowModelsBudgetCertificate.controlled,
      sampleUniformJensenWindowModelsBudgetCertificate]
  · norm_num [UniformJensenWindowModelsBudgetCertificate.budgetControlled,
      sampleUniformJensenWindowModelsBudgetCertificate]

example :
    sampleUniformJensenWindowModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleUniformJensenWindowModelsBudgetCertificate.size := by
  apply uniformJensenWindowModels_budgetCertificate_le_size
  constructor
  · norm_num [UniformJensenWindowModelsBudgetCertificate.controlled,
      sampleUniformJensenWindowModelsBudgetCertificate]
  · norm_num [UniformJensenWindowModelsBudgetCertificate.budgetControlled,
      sampleUniformJensenWindowModelsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List UniformJensenWindowModelsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleUniformJensenWindowModelsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleUniformJensenWindowModelsBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppB.UniformJensenWindowModels
