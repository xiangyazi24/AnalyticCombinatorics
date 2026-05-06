import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Laplace Tauberian schema bookkeeping.

The finite data records Laplace scale, monotonicity, and remainder control.
-/

namespace AnalyticCombinatorics.AppC.LaplaceTauberianSchemas

structure LaplaceTauberianData where
  laplaceScale : ℕ
  monotoneMass : Prop
  remainderBudget : ℕ
deriving Repr

def positiveLaplaceScale (d : LaplaceTauberianData) : Prop :=
  0 < d.laplaceScale

def laplaceTauberianReady (d : LaplaceTauberianData) : Prop :=
  positiveLaplaceScale d ∧ d.monotoneMass

def laplaceTauberianBudget (d : LaplaceTauberianData) : ℕ :=
  d.laplaceScale + d.remainderBudget

theorem laplaceTauberianReady.monotone {d : LaplaceTauberianData}
    (h : laplaceTauberianReady d) :
    d.monotoneMass := by
  rcases h with ⟨hleft, hright⟩
  exact hright

theorem laplaceScale_le_budget (d : LaplaceTauberianData) :
    d.laplaceScale ≤ laplaceTauberianBudget d := by
  unfold laplaceTauberianBudget
  omega

def sampleLaplaceTauberian : LaplaceTauberianData :=
  { laplaceScale := 6, monotoneMass := 4 ≤ 6, remainderBudget := 4 }

example : laplaceTauberianReady sampleLaplaceTauberian := by
  norm_num [laplaceTauberianReady, positiveLaplaceScale, sampleLaplaceTauberian]

example : laplaceTauberianBudget sampleLaplaceTauberian = 10 := by
  native_decide

structure LaplaceWindow where
  scale : ℕ
  transformMass : ℕ
  summatoryMass : ℕ
  remainderBudget : ℕ
deriving DecidableEq, Repr

def LaplaceWindow.scaleReady (w : LaplaceWindow) : Prop :=
  0 < w.scale

def LaplaceWindow.massControlled (w : LaplaceWindow) : Prop :=
  w.transformMass ≤ w.summatoryMass + w.remainderBudget

def LaplaceWindow.ready (w : LaplaceWindow) : Prop :=
  w.scaleReady ∧ w.massControlled

def LaplaceWindow.certificate (w : LaplaceWindow) : ℕ :=
  w.scale + w.transformMass + w.summatoryMass + w.remainderBudget

theorem transformMass_le_certificate (w : LaplaceWindow) :
    w.transformMass ≤ w.certificate := by
  unfold LaplaceWindow.certificate
  omega

def sampleLaplaceWindow : LaplaceWindow :=
  { scale := 6, transformMass := 14, summatoryMass := 10, remainderBudget := 4 }

example : sampleLaplaceWindow.ready := by
  norm_num [sampleLaplaceWindow, LaplaceWindow.ready, LaplaceWindow.scaleReady,
    LaplaceWindow.massControlled]

structure LaplaceRefinementWindow where
  scaleWindow : ℕ
  transformWindow : ℕ
  summatoryWindow : ℕ
  laplaceBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def LaplaceRefinementWindow.transformControlled
    (w : LaplaceRefinementWindow) : Prop :=
  w.transformWindow ≤ w.summatoryWindow + w.slack

def laplaceRefinementWindowReady (w : LaplaceRefinementWindow) : Prop :=
  0 < w.scaleWindow ∧ w.transformControlled ∧
    w.laplaceBudget ≤ w.scaleWindow + w.transformWindow + w.summatoryWindow + w.slack

def LaplaceRefinementWindow.certificate (w : LaplaceRefinementWindow) : ℕ :=
  w.scaleWindow + w.transformWindow + w.summatoryWindow + w.laplaceBudget + w.slack

theorem laplaceRefinement_budget_le_certificate
    (w : LaplaceRefinementWindow) :
    w.laplaceBudget ≤ w.certificate := by
  unfold LaplaceRefinementWindow.certificate
  omega

def sampleLaplaceRefinementWindow : LaplaceRefinementWindow :=
  { scaleWindow := 6, transformWindow := 14, summatoryWindow := 10,
    laplaceBudget := 31, slack := 4 }

example : laplaceRefinementWindowReady sampleLaplaceRefinementWindow := by
  norm_num [laplaceRefinementWindowReady,
    LaplaceRefinementWindow.transformControlled, sampleLaplaceRefinementWindow]


structure LaplaceTauberianSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def LaplaceTauberianSchemasBudgetCertificate.controlled
    (c : LaplaceTauberianSchemasBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def LaplaceTauberianSchemasBudgetCertificate.budgetControlled
    (c : LaplaceTauberianSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def LaplaceTauberianSchemasBudgetCertificate.Ready
    (c : LaplaceTauberianSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def LaplaceTauberianSchemasBudgetCertificate.size
    (c : LaplaceTauberianSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem laplaceTauberianSchemas_budgetCertificate_le_size
    (c : LaplaceTauberianSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleLaplaceTauberianSchemasBudgetCertificate :
    LaplaceTauberianSchemasBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

example : sampleLaplaceTauberianSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [LaplaceTauberianSchemasBudgetCertificate.controlled,
      sampleLaplaceTauberianSchemasBudgetCertificate]
  · norm_num [LaplaceTauberianSchemasBudgetCertificate.budgetControlled,
      sampleLaplaceTauberianSchemasBudgetCertificate]

example :
    sampleLaplaceTauberianSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleLaplaceTauberianSchemasBudgetCertificate.size := by
  apply laplaceTauberianSchemas_budgetCertificate_le_size
  constructor
  · norm_num [LaplaceTauberianSchemasBudgetCertificate.controlled,
      sampleLaplaceTauberianSchemasBudgetCertificate]
  · norm_num [LaplaceTauberianSchemasBudgetCertificate.budgetControlled,
      sampleLaplaceTauberianSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleLaplaceTauberianSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [LaplaceTauberianSchemasBudgetCertificate.controlled,
      sampleLaplaceTauberianSchemasBudgetCertificate]
  · norm_num [LaplaceTauberianSchemasBudgetCertificate.budgetControlled,
      sampleLaplaceTauberianSchemasBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleLaplaceTauberianSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleLaplaceTauberianSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List LaplaceTauberianSchemasBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleLaplaceTauberianSchemasBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleLaplaceTauberianSchemasBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppC.LaplaceTauberianSchemas
