import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Subcritical window schemas.

The finite record stores composition depth, subcritical margin, and
perturbation slack.
-/

namespace AnalyticCombinatorics.PartB.Ch7.SubcriticalWindowSchemas

structure SubcriticalWindowData where
  compositionDepth : ℕ
  subcriticalMargin : ℕ
  perturbationSlack : ℕ
deriving DecidableEq, Repr

def subcriticalMarginPositive (d : SubcriticalWindowData) : Prop :=
  0 < d.subcriticalMargin

def compositionDepthControlled (d : SubcriticalWindowData) : Prop :=
  d.compositionDepth ≤ d.subcriticalMargin + d.perturbationSlack

def subcriticalWindowReady (d : SubcriticalWindowData) : Prop :=
  subcriticalMarginPositive d ∧ compositionDepthControlled d

def subcriticalWindowBudget (d : SubcriticalWindowData) : ℕ :=
  d.compositionDepth + d.subcriticalMargin + d.perturbationSlack

theorem subcriticalWindowReady.margin {d : SubcriticalWindowData}
    (h : subcriticalWindowReady d) :
    subcriticalMarginPositive d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem compositionDepth_le_subcriticalBudget (d : SubcriticalWindowData) :
    d.compositionDepth ≤ subcriticalWindowBudget d := by
  unfold subcriticalWindowBudget
  omega

def sampleSubcriticalWindowData : SubcriticalWindowData :=
  { compositionDepth := 6, subcriticalMargin := 4, perturbationSlack := 3 }

example : subcriticalWindowReady sampleSubcriticalWindowData := by
  norm_num [subcriticalWindowReady, subcriticalMarginPositive]
  norm_num [compositionDepthControlled, sampleSubcriticalWindowData]

example : subcriticalWindowBudget sampleSubcriticalWindowData = 13 := by
  native_decide

structure SubcriticalCertificateWindow where
  compositionDepth : ℕ
  subcriticalMargin : ℕ
  perturbationSlack : ℕ
  transferBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def SubcriticalCertificateWindow.depthControlled (w : SubcriticalCertificateWindow) : Prop :=
  w.compositionDepth ≤ w.subcriticalMargin + w.perturbationSlack + w.slack

def SubcriticalCertificateWindow.transferControlled (w : SubcriticalCertificateWindow) : Prop :=
  w.transferBudget ≤ w.compositionDepth + w.subcriticalMargin + w.perturbationSlack + w.slack

def subcriticalCertificateReady (w : SubcriticalCertificateWindow) : Prop :=
  0 < w.subcriticalMargin ∧
    w.depthControlled ∧
    w.transferControlled

def SubcriticalCertificateWindow.certificate (w : SubcriticalCertificateWindow) : ℕ :=
  w.compositionDepth + w.subcriticalMargin + w.perturbationSlack + w.slack

theorem subcritical_transferBudget_le_certificate {w : SubcriticalCertificateWindow}
    (h : subcriticalCertificateReady w) :
    w.transferBudget ≤ w.certificate := by
  rcases h with ⟨_, _, htransfer⟩
  exact htransfer

def sampleSubcriticalCertificateWindow : SubcriticalCertificateWindow :=
  { compositionDepth := 6, subcriticalMargin := 4, perturbationSlack := 3, transferBudget := 12,
    slack := 0 }

example : subcriticalCertificateReady sampleSubcriticalCertificateWindow := by
  norm_num [subcriticalCertificateReady, SubcriticalCertificateWindow.depthControlled,
    SubcriticalCertificateWindow.transferControlled, sampleSubcriticalCertificateWindow]

example : sampleSubcriticalCertificateWindow.certificate = 13 := by
  native_decide


structure SubcriticalWindowSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def SubcriticalWindowSchemasBudgetCertificate.controlled
    (c : SubcriticalWindowSchemasBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def SubcriticalWindowSchemasBudgetCertificate.budgetControlled
    (c : SubcriticalWindowSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def SubcriticalWindowSchemasBudgetCertificate.Ready
    (c : SubcriticalWindowSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def SubcriticalWindowSchemasBudgetCertificate.size
    (c : SubcriticalWindowSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem subcriticalWindowSchemas_budgetCertificate_le_size
    (c : SubcriticalWindowSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleSubcriticalWindowSchemasBudgetCertificate :
    SubcriticalWindowSchemasBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleSubcriticalWindowSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [SubcriticalWindowSchemasBudgetCertificate.controlled,
      sampleSubcriticalWindowSchemasBudgetCertificate]
  · norm_num [SubcriticalWindowSchemasBudgetCertificate.budgetControlled,
      sampleSubcriticalWindowSchemasBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleSubcriticalWindowSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleSubcriticalWindowSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleSubcriticalWindowSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [SubcriticalWindowSchemasBudgetCertificate.controlled,
      sampleSubcriticalWindowSchemasBudgetCertificate]
  · norm_num [SubcriticalWindowSchemasBudgetCertificate.budgetControlled,
      sampleSubcriticalWindowSchemasBudgetCertificate]

example :
    sampleSubcriticalWindowSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleSubcriticalWindowSchemasBudgetCertificate.size := by
  apply subcriticalWindowSchemas_budgetCertificate_le_size
  constructor
  · norm_num [SubcriticalWindowSchemasBudgetCertificate.controlled,
      sampleSubcriticalWindowSchemasBudgetCertificate]
  · norm_num [SubcriticalWindowSchemasBudgetCertificate.budgetControlled,
      sampleSubcriticalWindowSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List SubcriticalWindowSchemasBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleSubcriticalWindowSchemasBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleSubcriticalWindowSchemasBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch7.SubcriticalWindowSchemas
