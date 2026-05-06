import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Multiscale saddle schemas.

The finite schema records primary scale, secondary scale, and remainder
slack.
-/

namespace AnalyticCombinatorics.PartB.Ch8.MultiscaleSaddleSchemas

structure MultiscaleSaddleData where
  primaryScale : ℕ
  secondaryScale : ℕ
  remainderSlack : ℕ
deriving DecidableEq, Repr

def primaryScalePositive (d : MultiscaleSaddleData) : Prop :=
  0 < d.primaryScale

def secondaryScaleControlled (d : MultiscaleSaddleData) : Prop :=
  d.secondaryScale ≤ d.primaryScale + d.remainderSlack

def multiscaleSaddleReady (d : MultiscaleSaddleData) : Prop :=
  primaryScalePositive d ∧ secondaryScaleControlled d

def multiscaleSaddleBudget (d : MultiscaleSaddleData) : ℕ :=
  d.primaryScale + d.secondaryScale + d.remainderSlack

theorem multiscaleSaddleReady.primary {d : MultiscaleSaddleData}
    (h : multiscaleSaddleReady d) :
    primaryScalePositive d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem secondaryScale_le_multiscaleBudget (d : MultiscaleSaddleData) :
    d.secondaryScale ≤ multiscaleSaddleBudget d := by
  unfold multiscaleSaddleBudget
  omega

def sampleMultiscaleSaddleData : MultiscaleSaddleData :=
  { primaryScale := 7, secondaryScale := 9, remainderSlack := 3 }

example : multiscaleSaddleReady sampleMultiscaleSaddleData := by
  norm_num [multiscaleSaddleReady, primaryScalePositive]
  norm_num [secondaryScaleControlled, sampleMultiscaleSaddleData]

example : multiscaleSaddleBudget sampleMultiscaleSaddleData = 19 := by
  native_decide

structure MultiscaleSaddleWindow where
  primaryScale : ℕ
  secondaryScale : ℕ
  remainderSlack : ℕ
  transitionBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def MultiscaleSaddleWindow.secondaryControlled (w : MultiscaleSaddleWindow) : Prop :=
  w.secondaryScale ≤ w.primaryScale + w.remainderSlack + w.slack

def MultiscaleSaddleWindow.transitionControlled (w : MultiscaleSaddleWindow) : Prop :=
  w.transitionBudget ≤ w.primaryScale + w.secondaryScale + w.remainderSlack + w.slack

def multiscaleSaddleWindowReady (w : MultiscaleSaddleWindow) : Prop :=
  0 < w.primaryScale ∧
    w.secondaryControlled ∧
    w.transitionControlled

def MultiscaleSaddleWindow.certificate (w : MultiscaleSaddleWindow) : ℕ :=
  w.primaryScale + w.secondaryScale + w.remainderSlack + w.slack

theorem multiscaleSaddle_transitionBudget_le_certificate {w : MultiscaleSaddleWindow}
    (h : multiscaleSaddleWindowReady w) :
    w.transitionBudget ≤ w.certificate := by
  rcases h with ⟨_, _, htransition⟩
  exact htransition

def sampleMultiscaleSaddleWindow : MultiscaleSaddleWindow :=
  { primaryScale := 7, secondaryScale := 9, remainderSlack := 3, transitionBudget := 18,
    slack := 0 }

example : multiscaleSaddleWindowReady sampleMultiscaleSaddleWindow := by
  norm_num [multiscaleSaddleWindowReady, MultiscaleSaddleWindow.secondaryControlled,
    MultiscaleSaddleWindow.transitionControlled, sampleMultiscaleSaddleWindow]

example : sampleMultiscaleSaddleWindow.certificate = 19 := by
  native_decide


structure MultiscaleSaddleSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def MultiscaleSaddleSchemasBudgetCertificate.controlled
    (c : MultiscaleSaddleSchemasBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def MultiscaleSaddleSchemasBudgetCertificate.budgetControlled
    (c : MultiscaleSaddleSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def MultiscaleSaddleSchemasBudgetCertificate.Ready
    (c : MultiscaleSaddleSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def MultiscaleSaddleSchemasBudgetCertificate.size
    (c : MultiscaleSaddleSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem multiscaleSaddleSchemas_budgetCertificate_le_size
    (c : MultiscaleSaddleSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleMultiscaleSaddleSchemasBudgetCertificate :
    MultiscaleSaddleSchemasBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleMultiscaleSaddleSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [MultiscaleSaddleSchemasBudgetCertificate.controlled,
      sampleMultiscaleSaddleSchemasBudgetCertificate]
  · norm_num [MultiscaleSaddleSchemasBudgetCertificate.budgetControlled,
      sampleMultiscaleSaddleSchemasBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleMultiscaleSaddleSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleMultiscaleSaddleSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleMultiscaleSaddleSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [MultiscaleSaddleSchemasBudgetCertificate.controlled,
      sampleMultiscaleSaddleSchemasBudgetCertificate]
  · norm_num [MultiscaleSaddleSchemasBudgetCertificate.budgetControlled,
      sampleMultiscaleSaddleSchemasBudgetCertificate]

example :
    sampleMultiscaleSaddleSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleMultiscaleSaddleSchemasBudgetCertificate.size := by
  apply multiscaleSaddleSchemas_budgetCertificate_le_size
  constructor
  · norm_num [MultiscaleSaddleSchemasBudgetCertificate.controlled,
      sampleMultiscaleSaddleSchemasBudgetCertificate]
  · norm_num [MultiscaleSaddleSchemasBudgetCertificate.budgetControlled,
      sampleMultiscaleSaddleSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List MultiscaleSaddleSchemasBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleMultiscaleSaddleSchemasBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleMultiscaleSaddleSchemasBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch8.MultiscaleSaddleSchemas
