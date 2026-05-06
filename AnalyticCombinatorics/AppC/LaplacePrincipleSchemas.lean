import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Laplace principle schemas.

The finite record stores speed, rate-function budget, and exponential
tightness slack.
-/

namespace AnalyticCombinatorics.AppC.LaplacePrincipleSchemas

structure LaplacePrincipleData where
  speed : ℕ
  rateBudget : ℕ
  tightnessSlack : ℕ
deriving DecidableEq, Repr

def speedPositive (d : LaplacePrincipleData) : Prop :=
  0 < d.speed

def rateControlled (d : LaplacePrincipleData) : Prop :=
  d.rateBudget ≤ d.speed + d.tightnessSlack

def laplacePrincipleReady (d : LaplacePrincipleData) : Prop :=
  speedPositive d ∧ rateControlled d

def laplacePrincipleBudget (d : LaplacePrincipleData) : ℕ :=
  d.speed + d.rateBudget + d.tightnessSlack

theorem laplacePrincipleReady.speed {d : LaplacePrincipleData}
    (h : laplacePrincipleReady d) :
    speedPositive d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem rateBudget_le_laplaceBudget (d : LaplacePrincipleData) :
    d.rateBudget ≤ laplacePrincipleBudget d := by
  unfold laplacePrincipleBudget
  omega

def sampleLaplacePrincipleData : LaplacePrincipleData :=
  { speed := 8, rateBudget := 10, tightnessSlack := 3 }

example : laplacePrincipleReady sampleLaplacePrincipleData := by
  norm_num [laplacePrincipleReady, speedPositive]
  norm_num [rateControlled, sampleLaplacePrincipleData]

example : laplacePrincipleBudget sampleLaplacePrincipleData = 21 := by
  native_decide

structure LaplacePrincipleWindow where
  speed : ℕ
  rateBudget : ℕ
  tightnessSlack : ℕ
  variationalBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def LaplacePrincipleWindow.rateControlled (w : LaplacePrincipleWindow) : Prop :=
  w.rateBudget ≤ w.speed + w.tightnessSlack + w.slack

def LaplacePrincipleWindow.variationalControlled (w : LaplacePrincipleWindow) : Prop :=
  w.variationalBudget ≤ w.speed + w.rateBudget + w.tightnessSlack + w.slack

def laplacePrincipleWindowReady (w : LaplacePrincipleWindow) : Prop :=
  0 < w.speed ∧
    w.rateControlled ∧
    w.variationalControlled

def LaplacePrincipleWindow.certificate (w : LaplacePrincipleWindow) : ℕ :=
  w.speed + w.rateBudget + w.tightnessSlack + w.slack

theorem laplacePrinciple_variationalBudget_le_certificate {w : LaplacePrincipleWindow}
    (h : laplacePrincipleWindowReady w) :
    w.variationalBudget ≤ w.certificate := by
  rcases h with ⟨_, _, hvariational⟩
  exact hvariational

def sampleLaplacePrincipleWindow : LaplacePrincipleWindow :=
  { speed := 8, rateBudget := 10, tightnessSlack := 3, variationalBudget := 20, slack := 0 }

example : laplacePrincipleWindowReady sampleLaplacePrincipleWindow := by
  norm_num [laplacePrincipleWindowReady, LaplacePrincipleWindow.rateControlled,
    LaplacePrincipleWindow.variationalControlled, sampleLaplacePrincipleWindow]

example : sampleLaplacePrincipleWindow.certificate = 21 := by
  native_decide


structure LaplacePrincipleSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def LaplacePrincipleSchemasBudgetCertificate.controlled
    (c : LaplacePrincipleSchemasBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def LaplacePrincipleSchemasBudgetCertificate.budgetControlled
    (c : LaplacePrincipleSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def LaplacePrincipleSchemasBudgetCertificate.Ready
    (c : LaplacePrincipleSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def LaplacePrincipleSchemasBudgetCertificate.size
    (c : LaplacePrincipleSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem laplacePrincipleSchemas_budgetCertificate_le_size
    (c : LaplacePrincipleSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleLaplacePrincipleSchemasBudgetCertificate :
    LaplacePrincipleSchemasBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleLaplacePrincipleSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [LaplacePrincipleSchemasBudgetCertificate.controlled,
      sampleLaplacePrincipleSchemasBudgetCertificate]
  · norm_num [LaplacePrincipleSchemasBudgetCertificate.budgetControlled,
      sampleLaplacePrincipleSchemasBudgetCertificate]

example : sampleLaplacePrincipleSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [LaplacePrincipleSchemasBudgetCertificate.controlled,
      sampleLaplacePrincipleSchemasBudgetCertificate]
  · norm_num [LaplacePrincipleSchemasBudgetCertificate.budgetControlled,
      sampleLaplacePrincipleSchemasBudgetCertificate]

example :
    sampleLaplacePrincipleSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleLaplacePrincipleSchemasBudgetCertificate.size := by
  apply laplacePrincipleSchemas_budgetCertificate_le_size
  constructor
  · norm_num [LaplacePrincipleSchemasBudgetCertificate.controlled,
      sampleLaplacePrincipleSchemasBudgetCertificate]
  · norm_num [LaplacePrincipleSchemasBudgetCertificate.budgetControlled,
      sampleLaplacePrincipleSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_le_size :
    sampleLaplacePrincipleSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleLaplacePrincipleSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List LaplacePrincipleSchemasBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleLaplacePrincipleSchemasBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleLaplacePrincipleSchemasBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppC.LaplacePrincipleSchemas
