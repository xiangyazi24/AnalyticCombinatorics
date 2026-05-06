import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Singularity exclusion windows.

This module records finite bookkeeping for exclusion windows: a positive
exclusion radius controls the singularity count with a margin slack.
-/

namespace AnalyticCombinatorics.Asymptotics.SingularityExclusionWindows

structure SingularityExclusionData where
  exclusionRadius : ℕ
  singularityCount : ℕ
  marginSlack : ℕ
deriving DecidableEq, Repr

def hasExclusionRadius (d : SingularityExclusionData) : Prop :=
  0 < d.exclusionRadius

def singularityCountControlled (d : SingularityExclusionData) : Prop :=
  d.singularityCount ≤ d.exclusionRadius + d.marginSlack

def singularityExclusionReady (d : SingularityExclusionData) : Prop :=
  hasExclusionRadius d ∧ singularityCountControlled d

def singularityExclusionBudget (d : SingularityExclusionData) : ℕ :=
  d.exclusionRadius + d.singularityCount + d.marginSlack

theorem singularityExclusionReady.hasExclusionRadius
    {d : SingularityExclusionData}
    (h : singularityExclusionReady d) :
    hasExclusionRadius d ∧ singularityCountControlled d ∧
      d.singularityCount ≤ singularityExclusionBudget d := by
  refine ⟨h.1, h.2, ?_⟩
  unfold singularityExclusionBudget
  omega

theorem singularityCount_le_budget (d : SingularityExclusionData) :
    d.singularityCount ≤ singularityExclusionBudget d := by
  unfold singularityExclusionBudget
  omega

def sampleSingularityExclusionData : SingularityExclusionData :=
  { exclusionRadius := 6, singularityCount := 8, marginSlack := 3 }

example : singularityExclusionReady sampleSingularityExclusionData := by
  norm_num [singularityExclusionReady, hasExclusionRadius]
  norm_num [singularityCountControlled, sampleSingularityExclusionData]

example : singularityExclusionBudget sampleSingularityExclusionData = 17 := by
  native_decide

/-- Finite executable readiness audit for singularity exclusion data. -/
def singularityExclusionDataListReady
    (data : List SingularityExclusionData) : Bool :=
  data.all fun d =>
    0 < d.exclusionRadius && d.singularityCount ≤ d.exclusionRadius + d.marginSlack

theorem singularityExclusionDataList_readyWindow :
    singularityExclusionDataListReady
      [{ exclusionRadius := 4, singularityCount := 5, marginSlack := 1 },
       { exclusionRadius := 6, singularityCount := 8, marginSlack := 3 }] =
      true := by
  unfold singularityExclusionDataListReady
  native_decide

/-- A certificate window for singularity exclusion. -/
structure SingularityExclusionCertificateWindow where
  exclusionWindow : ℕ
  singularityWindow : ℕ
  marginSlack : ℕ
  certificateBudget : ℕ
  slack : ℕ

/-- The singularity window is controlled by the exclusion window. -/
def singularityExclusionCertificateControlled
    (w : SingularityExclusionCertificateWindow) : Prop :=
  w.singularityWindow ≤ w.exclusionWindow + w.marginSlack + w.slack

/-- Readiness for a singularity exclusion certificate. -/
def singularityExclusionCertificateReady
    (w : SingularityExclusionCertificateWindow) : Prop :=
  0 < w.exclusionWindow ∧
    singularityExclusionCertificateControlled w ∧
      w.certificateBudget ≤ w.exclusionWindow + w.singularityWindow + w.slack

/-- Total size of a singularity exclusion certificate. -/
def singularityExclusionCertificate
    (w : SingularityExclusionCertificateWindow) : ℕ :=
  w.exclusionWindow + w.singularityWindow + w.marginSlack +
    w.certificateBudget + w.slack

theorem singularityExclusionCertificate_budget_le_certificate
    (w : SingularityExclusionCertificateWindow)
    (h : singularityExclusionCertificateReady w) :
    w.certificateBudget ≤ singularityExclusionCertificate w := by
  rcases h with ⟨_, _, hbudget⟩
  unfold singularityExclusionCertificate
  omega

def sampleSingularityExclusionCertificateWindow :
    SingularityExclusionCertificateWindow where
  exclusionWindow := 6
  singularityWindow := 7
  marginSlack := 2
  certificateBudget := 12
  slack := 1

example :
    singularityExclusionCertificateReady
      sampleSingularityExclusionCertificateWindow := by
  norm_num [singularityExclusionCertificateReady,
    singularityExclusionCertificateControlled,
    sampleSingularityExclusionCertificateWindow]

example :
    sampleSingularityExclusionCertificateWindow.certificateBudget ≤
      singularityExclusionCertificate
        sampleSingularityExclusionCertificateWindow := by
  apply singularityExclusionCertificate_budget_le_certificate
  norm_num [singularityExclusionCertificateReady,
    singularityExclusionCertificateControlled,
    sampleSingularityExclusionCertificateWindow]

structure SingularityExclusionRefinementCertificate where
  exclusionWindow : ℕ
  singularityWindow : ℕ
  marginSlackWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def SingularityExclusionRefinementCertificate.singularityControlled
    (c : SingularityExclusionRefinementCertificate) : Prop :=
  c.singularityWindow ≤ c.exclusionWindow + c.marginSlackWindow + c.slack

def SingularityExclusionRefinementCertificate.certificateBudgetControlled
    (c : SingularityExclusionRefinementCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.exclusionWindow + c.singularityWindow + c.marginSlackWindow + c.slack

def singularityExclusionRefinementReady
    (c : SingularityExclusionRefinementCertificate) : Prop :=
  0 < c.exclusionWindow ∧ c.singularityControlled ∧ c.certificateBudgetControlled

def SingularityExclusionRefinementCertificate.size
    (c : SingularityExclusionRefinementCertificate) : ℕ :=
  c.exclusionWindow + c.singularityWindow + c.marginSlackWindow + c.slack

theorem singularityExclusion_certificateBudgetWindow_le_size
    {c : SingularityExclusionRefinementCertificate}
    (h : singularityExclusionRefinementReady c) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, _, hbudget⟩
  exact hbudget

def sampleSingularityExclusionRefinementCertificate :
    SingularityExclusionRefinementCertificate :=
  { exclusionWindow := 6, singularityWindow := 7, marginSlackWindow := 2,
    certificateBudgetWindow := 16, slack := 1 }

example : singularityExclusionRefinementReady
    sampleSingularityExclusionRefinementCertificate := by
  norm_num [singularityExclusionRefinementReady,
    SingularityExclusionRefinementCertificate.singularityControlled,
    SingularityExclusionRefinementCertificate.certificateBudgetControlled,
    sampleSingularityExclusionRefinementCertificate]

example :
    sampleSingularityExclusionRefinementCertificate.certificateBudgetWindow ≤
      sampleSingularityExclusionRefinementCertificate.size := by
  norm_num [SingularityExclusionRefinementCertificate.size,
    sampleSingularityExclusionRefinementCertificate]

structure SingularityExclusionBudgetCertificate where
  exclusionWindow : ℕ
  singularityWindow : ℕ
  marginSlackWindow : ℕ
  singularityBudgetWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def SingularityExclusionBudgetCertificate.controlled
    (c : SingularityExclusionBudgetCertificate) : Prop :=
  0 < c.exclusionWindow ∧
    c.singularityWindow ≤ c.exclusionWindow + c.marginSlackWindow + c.slack ∧
      c.singularityBudgetWindow ≤
        c.exclusionWindow + c.singularityWindow + c.marginSlackWindow + c.slack

def SingularityExclusionBudgetCertificate.budgetControlled
    (c : SingularityExclusionBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.exclusionWindow + c.singularityWindow + c.marginSlackWindow +
      c.singularityBudgetWindow + c.slack

def SingularityExclusionBudgetCertificate.Ready
    (c : SingularityExclusionBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def SingularityExclusionBudgetCertificate.size
    (c : SingularityExclusionBudgetCertificate) : ℕ :=
  c.exclusionWindow + c.singularityWindow + c.marginSlackWindow +
    c.singularityBudgetWindow + c.slack

theorem singularityExclusion_budgetCertificate_le_size
    (c : SingularityExclusionBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleSingularityExclusionBudgetCertificate :
    SingularityExclusionBudgetCertificate :=
  { exclusionWindow := 6
    singularityWindow := 7
    marginSlackWindow := 2
    singularityBudgetWindow := 16
    certificateBudgetWindow := 32
    slack := 1 }

example : sampleSingularityExclusionBudgetCertificate.Ready := by
  constructor
  · norm_num [SingularityExclusionBudgetCertificate.controlled,
      sampleSingularityExclusionBudgetCertificate]
  · norm_num [SingularityExclusionBudgetCertificate.budgetControlled,
      sampleSingularityExclusionBudgetCertificate]

example :
    sampleSingularityExclusionBudgetCertificate.certificateBudgetWindow ≤
      sampleSingularityExclusionBudgetCertificate.size := by
  apply singularityExclusion_budgetCertificate_le_size
  constructor
  · norm_num [SingularityExclusionBudgetCertificate.controlled,
      sampleSingularityExclusionBudgetCertificate]
  · norm_num [SingularityExclusionBudgetCertificate.budgetControlled,
      sampleSingularityExclusionBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleSingularityExclusionBudgetCertificate.Ready := by
  constructor
  · norm_num [SingularityExclusionBudgetCertificate.controlled,
      sampleSingularityExclusionBudgetCertificate]
  · norm_num [SingularityExclusionBudgetCertificate.budgetControlled,
      sampleSingularityExclusionBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleSingularityExclusionBudgetCertificate.certificateBudgetWindow ≤
      sampleSingularityExclusionBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady
    (data : List SingularityExclusionBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleSingularityExclusionBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleSingularityExclusionBudgetCertificate
  native_decide
end AnalyticCombinatorics.Asymptotics.SingularityExclusionWindows
