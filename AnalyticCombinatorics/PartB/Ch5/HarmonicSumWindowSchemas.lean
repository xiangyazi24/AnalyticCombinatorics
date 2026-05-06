import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Harmonic sum window schemas.

The finite schema records summation depth, Mellin window, and remainder
slack.
-/

namespace AnalyticCombinatorics.PartB.Ch5.HarmonicSumWindowSchemas

structure HarmonicSumWindowData where
  summationDepth : ℕ
  mellinWindow : ℕ
  remainderSlack : ℕ
deriving DecidableEq, Repr

def summationDepthPositive (d : HarmonicSumWindowData) : Prop :=
  0 < d.summationDepth

def mellinWindowControlled (d : HarmonicSumWindowData) : Prop :=
  d.mellinWindow ≤ d.summationDepth + d.remainderSlack

def harmonicSumWindowReady (d : HarmonicSumWindowData) : Prop :=
  summationDepthPositive d ∧ mellinWindowControlled d

def harmonicSumWindowBudget (d : HarmonicSumWindowData) : ℕ :=
  d.summationDepth + d.mellinWindow + d.remainderSlack

theorem harmonicSumWindowReady.depth {d : HarmonicSumWindowData}
    (h : harmonicSumWindowReady d) :
    summationDepthPositive d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem mellinWindow_le_harmonicSumBudget (d : HarmonicSumWindowData) :
    d.mellinWindow ≤ harmonicSumWindowBudget d := by
  unfold harmonicSumWindowBudget
  omega

def sampleHarmonicSumWindowData : HarmonicSumWindowData :=
  { summationDepth := 5, mellinWindow := 7, remainderSlack := 3 }

example : harmonicSumWindowReady sampleHarmonicSumWindowData := by
  norm_num [harmonicSumWindowReady, summationDepthPositive]
  norm_num [mellinWindowControlled, sampleHarmonicSumWindowData]

example : harmonicSumWindowBudget sampleHarmonicSumWindowData = 15 := by
  native_decide

structure HarmonicSumCertificateWindow where
  summationDepth : ℕ
  mellinWindow : ℕ
  remainderSlack : ℕ
  truncationBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def HarmonicSumCertificateWindow.mellinControlled
    (w : HarmonicSumCertificateWindow) : Prop :=
  w.mellinWindow ≤ w.summationDepth + w.remainderSlack + w.slack

def HarmonicSumCertificateWindow.truncationControlled
    (w : HarmonicSumCertificateWindow) : Prop :=
  w.truncationBudget ≤ w.summationDepth + w.mellinWindow + w.remainderSlack + w.slack

def harmonicSumCertificateReady (w : HarmonicSumCertificateWindow) : Prop :=
  0 < w.summationDepth ∧
    w.mellinControlled ∧
    w.truncationControlled

def HarmonicSumCertificateWindow.certificate (w : HarmonicSumCertificateWindow) : ℕ :=
  w.summationDepth + w.mellinWindow + w.remainderSlack + w.slack

theorem harmonicSum_truncationBudget_le_certificate {w : HarmonicSumCertificateWindow}
    (h : harmonicSumCertificateReady w) :
    w.truncationBudget ≤ w.certificate := by
  rcases h with ⟨_, _, htrunc⟩
  exact htrunc

def sampleHarmonicSumCertificateWindow : HarmonicSumCertificateWindow :=
  { summationDepth := 5, mellinWindow := 7, remainderSlack := 3, truncationBudget := 14,
    slack := 0 }

example : harmonicSumCertificateReady sampleHarmonicSumCertificateWindow := by
  norm_num [harmonicSumCertificateReady, HarmonicSumCertificateWindow.mellinControlled,
    HarmonicSumCertificateWindow.truncationControlled, sampleHarmonicSumCertificateWindow]

example : sampleHarmonicSumCertificateWindow.certificate = 15 := by
  native_decide


structure HarmonicSumWindowSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def HarmonicSumWindowSchemasBudgetCertificate.controlled
    (c : HarmonicSumWindowSchemasBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def HarmonicSumWindowSchemasBudgetCertificate.budgetControlled
    (c : HarmonicSumWindowSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def HarmonicSumWindowSchemasBudgetCertificate.Ready
    (c : HarmonicSumWindowSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def HarmonicSumWindowSchemasBudgetCertificate.size
    (c : HarmonicSumWindowSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem harmonicSumWindowSchemas_budgetCertificate_le_size
    (c : HarmonicSumWindowSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleHarmonicSumWindowSchemasBudgetCertificate :
    HarmonicSumWindowSchemasBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleHarmonicSumWindowSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [HarmonicSumWindowSchemasBudgetCertificate.controlled,
      sampleHarmonicSumWindowSchemasBudgetCertificate]
  · norm_num [HarmonicSumWindowSchemasBudgetCertificate.budgetControlled,
      sampleHarmonicSumWindowSchemasBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleHarmonicSumWindowSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleHarmonicSumWindowSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleHarmonicSumWindowSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [HarmonicSumWindowSchemasBudgetCertificate.controlled,
      sampleHarmonicSumWindowSchemasBudgetCertificate]
  · norm_num [HarmonicSumWindowSchemasBudgetCertificate.budgetControlled,
      sampleHarmonicSumWindowSchemasBudgetCertificate]

example :
    sampleHarmonicSumWindowSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleHarmonicSumWindowSchemasBudgetCertificate.size := by
  apply harmonicSumWindowSchemas_budgetCertificate_le_size
  constructor
  · norm_num [HarmonicSumWindowSchemasBudgetCertificate.controlled,
      sampleHarmonicSumWindowSchemasBudgetCertificate]
  · norm_num [HarmonicSumWindowSchemasBudgetCertificate.budgetControlled,
      sampleHarmonicSumWindowSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List HarmonicSumWindowSchemasBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleHarmonicSumWindowSchemasBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleHarmonicSumWindowSchemasBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch5.HarmonicSumWindowSchemas
