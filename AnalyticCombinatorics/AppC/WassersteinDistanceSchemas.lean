import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Wasserstein distance schemas.

The finite abstraction records transport cost, coupling budget, and
moment slack.
-/

namespace AnalyticCombinatorics.AppC.WassersteinDistanceSchemas

structure WassersteinDistanceData where
  transportCost : ℕ
  couplingBudget : ℕ
  momentSlack : ℕ
deriving DecidableEq, Repr

def couplingNonempty (d : WassersteinDistanceData) : Prop :=
  0 < d.couplingBudget

def costControlled (d : WassersteinDistanceData) : Prop :=
  d.transportCost ≤ d.couplingBudget + d.momentSlack

def wassersteinDistanceReady (d : WassersteinDistanceData) : Prop :=
  couplingNonempty d ∧ costControlled d

def wassersteinDistanceBudget (d : WassersteinDistanceData) : ℕ :=
  d.transportCost + d.couplingBudget + d.momentSlack

theorem wassersteinDistanceReady.coupling
    {d : WassersteinDistanceData}
    (h : wassersteinDistanceReady d) :
    couplingNonempty d ∧ costControlled d ∧ d.transportCost ≤ wassersteinDistanceBudget d := by
  refine ⟨h.1, h.2, ?_⟩
  unfold wassersteinDistanceBudget
  omega

theorem transportCost_le_wassersteinBudget
    (d : WassersteinDistanceData) :
    d.transportCost ≤ wassersteinDistanceBudget d := by
  unfold wassersteinDistanceBudget
  omega

def sampleWassersteinDistanceData : WassersteinDistanceData :=
  { transportCost := 6, couplingBudget := 4, momentSlack := 5 }

example : wassersteinDistanceReady sampleWassersteinDistanceData := by
  norm_num [wassersteinDistanceReady, couplingNonempty]
  norm_num [costControlled, sampleWassersteinDistanceData]

example : wassersteinDistanceBudget sampleWassersteinDistanceData = 15 := by
  native_decide

structure WassersteinDistanceWindow where
  costWindow : ℕ
  couplingWindow : ℕ
  momentSlack : ℕ
  distanceBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def WassersteinDistanceWindow.costControlled (w : WassersteinDistanceWindow) : Prop :=
  w.costWindow ≤ w.couplingWindow + w.momentSlack + w.slack

def wassersteinDistanceWindowReady (w : WassersteinDistanceWindow) : Prop :=
  0 < w.couplingWindow ∧ w.costControlled ∧
    w.distanceBudget ≤ w.costWindow + w.couplingWindow + w.slack

def WassersteinDistanceWindow.certificate (w : WassersteinDistanceWindow) : ℕ :=
  w.costWindow + w.couplingWindow + w.momentSlack + w.distanceBudget + w.slack

theorem wassersteinDistance_distanceBudget_le_certificate
    (w : WassersteinDistanceWindow) :
    w.distanceBudget ≤ w.certificate := by
  unfold WassersteinDistanceWindow.certificate
  omega

def sampleWassersteinDistanceWindow : WassersteinDistanceWindow :=
  { costWindow := 5, couplingWindow := 4, momentSlack := 2, distanceBudget := 10, slack := 1 }

example : wassersteinDistanceWindowReady sampleWassersteinDistanceWindow := by
  norm_num [wassersteinDistanceWindowReady, WassersteinDistanceWindow.costControlled,
    sampleWassersteinDistanceWindow]


structure WassersteinDistanceSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def WassersteinDistanceSchemasBudgetCertificate.controlled
    (c : WassersteinDistanceSchemasBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def WassersteinDistanceSchemasBudgetCertificate.budgetControlled
    (c : WassersteinDistanceSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def WassersteinDistanceSchemasBudgetCertificate.Ready
    (c : WassersteinDistanceSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def WassersteinDistanceSchemasBudgetCertificate.size
    (c : WassersteinDistanceSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem wassersteinDistanceSchemas_budgetCertificate_le_size
    (c : WassersteinDistanceSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleWassersteinDistanceSchemasBudgetCertificate :
    WassersteinDistanceSchemasBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleWassersteinDistanceSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [WassersteinDistanceSchemasBudgetCertificate.controlled,
      sampleWassersteinDistanceSchemasBudgetCertificate]
  · norm_num [WassersteinDistanceSchemasBudgetCertificate.budgetControlled,
      sampleWassersteinDistanceSchemasBudgetCertificate]

example : sampleWassersteinDistanceSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [WassersteinDistanceSchemasBudgetCertificate.controlled,
      sampleWassersteinDistanceSchemasBudgetCertificate]
  · norm_num [WassersteinDistanceSchemasBudgetCertificate.budgetControlled,
      sampleWassersteinDistanceSchemasBudgetCertificate]

example :
    sampleWassersteinDistanceSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleWassersteinDistanceSchemasBudgetCertificate.size := by
  apply wassersteinDistanceSchemas_budgetCertificate_le_size
  constructor
  · norm_num [WassersteinDistanceSchemasBudgetCertificate.controlled,
      sampleWassersteinDistanceSchemasBudgetCertificate]
  · norm_num [WassersteinDistanceSchemasBudgetCertificate.budgetControlled,
      sampleWassersteinDistanceSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_le_size :
    sampleWassersteinDistanceSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleWassersteinDistanceSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List WassersteinDistanceSchemasBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleWassersteinDistanceSchemasBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleWassersteinDistanceSchemasBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppC.WassersteinDistanceSchemas
