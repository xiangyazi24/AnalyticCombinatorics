import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Implicit critical window schemas.

The finite schema records critical radius, branching scale, and
perturbation slack.
-/

namespace AnalyticCombinatorics.PartB.Ch7.ImplicitCriticalWindowSchemas

structure ImplicitCriticalWindowData where
  criticalRadius : ℕ
  branchingScale : ℕ
  perturbationSlack : ℕ
deriving DecidableEq, Repr

def criticalRadiusPositive (d : ImplicitCriticalWindowData) : Prop :=
  0 < d.criticalRadius

def branchingScaleControlled (d : ImplicitCriticalWindowData) : Prop :=
  d.branchingScale ≤ d.criticalRadius + d.perturbationSlack

def implicitCriticalWindowReady (d : ImplicitCriticalWindowData) : Prop :=
  criticalRadiusPositive d ∧ branchingScaleControlled d

def implicitCriticalWindowBudget (d : ImplicitCriticalWindowData) : ℕ :=
  d.criticalRadius + d.branchingScale + d.perturbationSlack

theorem implicitCriticalWindowReady.radius
    {d : ImplicitCriticalWindowData}
    (h : implicitCriticalWindowReady d) :
    criticalRadiusPositive d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem branchingScale_le_implicitCriticalBudget
    (d : ImplicitCriticalWindowData) :
    d.branchingScale ≤ implicitCriticalWindowBudget d := by
  unfold implicitCriticalWindowBudget
  omega

def sampleImplicitCriticalWindowData : ImplicitCriticalWindowData :=
  { criticalRadius := 7, branchingScale := 9, perturbationSlack := 3 }

example : implicitCriticalWindowReady sampleImplicitCriticalWindowData := by
  norm_num [implicitCriticalWindowReady, criticalRadiusPositive]
  norm_num [branchingScaleControlled, sampleImplicitCriticalWindowData]

example : implicitCriticalWindowBudget sampleImplicitCriticalWindowData = 19 := by
  native_decide

structure ImplicitCriticalWindowBudgetCertificate where
  criticalRadiusWindow : ℕ
  branchingScaleWindow : ℕ
  perturbationSlackWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def ImplicitCriticalWindowBudgetCertificate.controlled
    (c : ImplicitCriticalWindowBudgetCertificate) : Prop :=
  0 < c.criticalRadiusWindow ∧
    c.branchingScaleWindow ≤
      c.criticalRadiusWindow + c.perturbationSlackWindow + c.slack

def ImplicitCriticalWindowBudgetCertificate.budgetControlled
    (c : ImplicitCriticalWindowBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.criticalRadiusWindow + c.branchingScaleWindow + c.perturbationSlackWindow +
      c.slack

def ImplicitCriticalWindowBudgetCertificate.Ready
    (c : ImplicitCriticalWindowBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def ImplicitCriticalWindowBudgetCertificate.size
    (c : ImplicitCriticalWindowBudgetCertificate) : ℕ :=
  c.criticalRadiusWindow + c.branchingScaleWindow + c.perturbationSlackWindow +
    c.slack

theorem implicitCriticalWindow_budgetCertificate_le_size
    (c : ImplicitCriticalWindowBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleImplicitCriticalWindowBudgetCertificate :
    ImplicitCriticalWindowBudgetCertificate :=
  { criticalRadiusWindow := 7
    branchingScaleWindow := 9
    perturbationSlackWindow := 3
    certificateBudgetWindow := 20
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleImplicitCriticalWindowBudgetCertificate.Ready := by
  constructor
  · norm_num [ImplicitCriticalWindowBudgetCertificate.controlled,
      sampleImplicitCriticalWindowBudgetCertificate]
  · norm_num [ImplicitCriticalWindowBudgetCertificate.budgetControlled,
      sampleImplicitCriticalWindowBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleImplicitCriticalWindowBudgetCertificate.certificateBudgetWindow ≤
      sampleImplicitCriticalWindowBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleImplicitCriticalWindowBudgetCertificate.Ready := by
  constructor
  · norm_num [ImplicitCriticalWindowBudgetCertificate.controlled,
      sampleImplicitCriticalWindowBudgetCertificate]
  · norm_num [ImplicitCriticalWindowBudgetCertificate.budgetControlled,
      sampleImplicitCriticalWindowBudgetCertificate]

example :
    sampleImplicitCriticalWindowBudgetCertificate.certificateBudgetWindow ≤
      sampleImplicitCriticalWindowBudgetCertificate.size := by
  apply implicitCriticalWindow_budgetCertificate_le_size
  constructor
  · norm_num [ImplicitCriticalWindowBudgetCertificate.controlled,
      sampleImplicitCriticalWindowBudgetCertificate]
  · norm_num [ImplicitCriticalWindowBudgetCertificate.budgetControlled,
      sampleImplicitCriticalWindowBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List ImplicitCriticalWindowBudgetCertificate) : Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady [sampleImplicitCriticalWindowBudgetCertificate] = true := by
  unfold budgetCertificateListReady sampleImplicitCriticalWindowBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch7.ImplicitCriticalWindowSchemas
