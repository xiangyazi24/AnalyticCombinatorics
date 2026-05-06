import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Uniform Harnack chain models.

This module records finite bookkeeping for Harnack chain windows.
-/

namespace AnalyticCombinatorics.AppB.UniformHarnackChainModels

structure HarnackChainData where
  chainLength : ℕ
  comparisonWindow : ℕ
  harnackSlack : ℕ
deriving DecidableEq, Repr

def hasChainLength (d : HarnackChainData) : Prop :=
  0 < d.chainLength

def comparisonWindowControlled (d : HarnackChainData) : Prop :=
  d.comparisonWindow ≤ d.chainLength + d.harnackSlack

def harnackChainReady (d : HarnackChainData) : Prop :=
  hasChainLength d ∧ comparisonWindowControlled d

def harnackChainBudget (d : HarnackChainData) : ℕ :=
  d.chainLength + d.comparisonWindow + d.harnackSlack

theorem harnackChainReady.hasChainLength {d : HarnackChainData}
    (h : harnackChainReady d) :
    hasChainLength d ∧ comparisonWindowControlled d ∧
      d.comparisonWindow ≤ harnackChainBudget d := by
  refine ⟨h.1, h.2, ?_⟩
  unfold harnackChainBudget
  omega

theorem comparisonWindow_le_budget (d : HarnackChainData) :
    d.comparisonWindow ≤ harnackChainBudget d := by
  unfold harnackChainBudget
  omega

def sampleHarnackChainData : HarnackChainData :=
  { chainLength := 6, comparisonWindow := 8, harnackSlack := 3 }

example : harnackChainReady sampleHarnackChainData := by
  norm_num [harnackChainReady, hasChainLength]
  norm_num [comparisonWindowControlled, sampleHarnackChainData]

example : harnackChainBudget sampleHarnackChainData = 17 := by
  native_decide

structure UniformHarnackChainWindow where
  chainWindow : ℕ
  comparisonWindow : ℕ
  harnackSlack : ℕ
  comparisonBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def UniformHarnackChainWindow.comparisonControlled
    (w : UniformHarnackChainWindow) : Prop :=
  w.comparisonWindow ≤ w.chainWindow + w.harnackSlack + w.slack

def uniformHarnackChainWindowReady (w : UniformHarnackChainWindow) : Prop :=
  0 < w.chainWindow ∧ w.comparisonControlled ∧
    w.comparisonBudget ≤ w.chainWindow + w.comparisonWindow + w.slack

def UniformHarnackChainWindow.certificate (w : UniformHarnackChainWindow) : ℕ :=
  w.chainWindow + w.comparisonWindow + w.harnackSlack + w.comparisonBudget + w.slack

theorem uniformHarnackChain_comparisonBudget_le_certificate
    (w : UniformHarnackChainWindow) :
    w.comparisonBudget ≤ w.certificate := by
  unfold UniformHarnackChainWindow.certificate
  omega

def sampleUniformHarnackChainWindow : UniformHarnackChainWindow :=
  { chainWindow := 5, comparisonWindow := 7, harnackSlack := 2,
    comparisonBudget := 14, slack := 2 }

example : uniformHarnackChainWindowReady sampleUniformHarnackChainWindow := by
  norm_num [uniformHarnackChainWindowReady,
    UniformHarnackChainWindow.comparisonControlled, sampleUniformHarnackChainWindow]


structure UniformHarnackChainModelsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def UniformHarnackChainModelsBudgetCertificate.controlled
    (c : UniformHarnackChainModelsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def UniformHarnackChainModelsBudgetCertificate.budgetControlled
    (c : UniformHarnackChainModelsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def UniformHarnackChainModelsBudgetCertificate.Ready
    (c : UniformHarnackChainModelsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def UniformHarnackChainModelsBudgetCertificate.size
    (c : UniformHarnackChainModelsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem uniformHarnackChainModels_budgetCertificate_le_size
    (c : UniformHarnackChainModelsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleUniformHarnackChainModelsBudgetCertificate :
    UniformHarnackChainModelsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleUniformHarnackChainModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [UniformHarnackChainModelsBudgetCertificate.controlled,
      sampleUniformHarnackChainModelsBudgetCertificate]
  · norm_num [UniformHarnackChainModelsBudgetCertificate.budgetControlled,
      sampleUniformHarnackChainModelsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleUniformHarnackChainModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleUniformHarnackChainModelsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleUniformHarnackChainModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [UniformHarnackChainModelsBudgetCertificate.controlled,
      sampleUniformHarnackChainModelsBudgetCertificate]
  · norm_num [UniformHarnackChainModelsBudgetCertificate.budgetControlled,
      sampleUniformHarnackChainModelsBudgetCertificate]

example :
    sampleUniformHarnackChainModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleUniformHarnackChainModelsBudgetCertificate.size := by
  apply uniformHarnackChainModels_budgetCertificate_le_size
  constructor
  · norm_num [UniformHarnackChainModelsBudgetCertificate.controlled,
      sampleUniformHarnackChainModelsBudgetCertificate]
  · norm_num [UniformHarnackChainModelsBudgetCertificate.budgetControlled,
      sampleUniformHarnackChainModelsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List UniformHarnackChainModelsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleUniformHarnackChainModelsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleUniformHarnackChainModelsBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppB.UniformHarnackChainModels
